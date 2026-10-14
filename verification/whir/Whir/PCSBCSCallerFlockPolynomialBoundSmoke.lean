import Whir.PCSBCSCallerFlockPolynomialBound

/-! Executable counted/source Flock projection fixtures. Arithmetic messages are
not honest proof witnesses: these tests check actual parser and claim assembly,
not sumcheck validity or cryptographic security. -/
namespace Whir.PCSBCSCallerFlockPolynomialBoundSmoke
open Concrete WHIRCallerClaims PCSBCSCallerParserCost

private def require (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

private def scalar (n : Nat) : E := E.ofK (UInt64.ofNat n)

private def layouts : List FlockLayout := [⟨0,6,7⟩,⟨64,8,7⟩]

private def slices (base : Nat) : List E := (List.range 64).map (fun i => scalar (base+i))

private def prelude : List CallerToken :=
  List.replicate 3 (.draw 0) ++ List.replicate 64 (.sent 0) ++ [.draw 0]

private def zcTokens : List CallerToken :=
  ((List.range 9).map (fun i => [.sent 0,.sent 0,.draw (scalar (10+i))])).flatten

private def fixture : List CallerToken :=
  prelude ++ zcTokens ++ List.replicate 6 (.sent 0) ++ [.draw 0] ++
    [.sent 0,.sent 0,.draw (scalar 40),.sent 0,.sent 0,.draw (scalar 41)] ++
    (slices 100).map CallerToken.sent ++ [.sent 0] ++
    (slices 200).map CallerToken.sent ++ [.sent 0]

private def project (claims : List RingPCSGame.FamilyClaim) :
    List (Nat × List E × List E) :=
  claims.map (fun c => (c.offset,c.point.toList,(List.finRange 64).map c.slices))

private def cap (ls : List FlockLayout) : Nat :=
  let s := flockConfigurationSize ls
  20*s^2+800*s+700

private def rejected (label : String) (ls : List FlockLayout) (tokens : List CallerToken) : IO Unit := do
  let counted := PCSBCSCallerParserCost.flockClaims ls tokens
  require (label ++ ": counted rejects") counted.result.isNone
  require (label ++ ": source rejects") (WHIRCallerClaims.flockClaims ls tokens).isNone
  require (label ++ ": rejection work remains bounded") (counted.work ≤ cap ls)
  require (label ++ ": reached work is retained") (0 < counted.work)

def smoke : IO Unit := do
  let suffix := [CallerToken.sent (scalar 777)]
  let counted := PCSBCSCallerParserCost.flockClaims layouts (fixture ++ suffix)
  let source := WHIRCallerClaims.flockClaims layouts (fixture ++ suffix)
  let expected : List (Nat × List E × List E) :=
    [(0,(List.range 7).map (fun i => scalar (10+i)),slices 100),
     (64,[scalar 41,scalar 40] ++ (List.range 7).map (fun i => scalar (12+i)),slices 200)]
  require "mixed counted claims preserve exact reverse/suffix points, slice blocks, offsets, and rest"
    (match counted.result with
     | some (claims,rest) => project claims == expected && rest == suffix
     | none => false)
  require "mixed source claims preserve exact reverse/suffix points, slice blocks, offsets, and rest"
    (match source with
     | some (claims,rest) => project claims == expected && rest == suffix
     | none => false)
  require "all accepted actual work is bounded by additive literal configuration size"
    (counted.work ≤ cap layouts)
  require "accepted producer count and unequal point dimensions are actual returned values"
    (match counted.result with
     | some (claims,_) => claims.length == 2 && claims.map (fun c => c.point.size) == [7,9]
     | none => false)
  rejected "empty layouts" [] fixture
  rejected "kLog below six" [⟨0,5,10⟩] fixture
  rejected "logN below thirteen" [⟨0,6,6⟩] fixture
  rejected "wrong initial challenge token" layouts [.sent 0]
  rejected "zerocheck rejects wrong challenge after reading both coefficients" layouts
    (prelude ++ [.sent 0,.sent 0,.sent 0])
  rejected "truncated final producer slice block" layouts (fixture.take (fixture.length-2))
  let early := PCSBCSCallerParserCost.flockClaims layouts [.sent 0]
  let late := PCSBCSCallerParserCost.flockClaims layouts (fixture.take (fixture.length-2))
  require "late failure retains strictly more work than prelude failure" (early.work < late.work)
  let zc := (List.range 9).map (fun i => scalar (10+i))
  let lc := [scalar 40,scalar 41]
  let assembled := PCSBCSCallerParserCost.assembleFlock ⟨64,8,7⟩ zc lc (slices 200)
  require "per-layout actual assembly returns exact dimensions and endpoint slices"
    (match assembled.value with
     | some c => c.point.toList == expected[1]!.2.1 &&
       c.slices ⟨0,by decide⟩ == scalar 200 && c.slices ⟨63,by decide⟩ == scalar 263
     | none => false)
  require "per-layout actual assembly counter satisfies its linear bound"
    (assembled.work ≤ 9*lc.length+6*zc.length+(slices 200).length+30)
  require "short lincheck metadata rejected by actual assembly"
    (PCSBCSCallerParserCost.assembleFlock ⟨64,8,7⟩ zc [scalar 40] (slices 200)).value.isNone
  require "short zerocheck metadata rejected by actual assembly"
    (PCSBCSCallerParserCost.assembleFlock ⟨64,8,7⟩ (zc.take 8) lc (slices 200)).value.isNone
  require "63-slice block rejected by actual assembly"
    (PCSBCSCallerParserCost.assembleFlock ⟨64,8,7⟩ zc lc ((slices 200).take 63)).value.isNone
  require "65-slice block rejected by actual assembly"
    (PCSBCSCallerParserCost.assembleFlock ⟨64,8,7⟩ zc lc (slices 200 ++ [scalar 264])).value.isNone
  require "deferred getter boundary prices remain separate from assembly"
    (assembleFlockGetterWork ⟨0,by decide⟩ == 2 && assembleFlockGetterWork ⟨63,by decide⟩ == 65)
  IO.println s!"counted/source flock runtime passed: accepted work={counted.work}, early rejection work={early.work}, late rejection work={late.work}, assembly work={assembled.work}, polynomial cap={cap layouts}"

end Whir.PCSBCSCallerFlockPolynomialBoundSmoke

def main : IO Unit := Whir.PCSBCSCallerFlockPolynomialBoundSmoke.smoke
