import Whir.PCSBCSCallerBusTablePolynomialBound

/-! Executed accepted/rejected public-token fixtures for the actual counted AIR
and bus receiver paths, compared with their source erasures and work bounds. -/
set_option autoImplicit false
namespace Whir.PCSBCSCallerBusTablePolynomialBoundSmoke
open Concrete WHIRCallerClaims

private def require (label : String) (ok : Bool) : IO Unit :=
  if ok then pure () else throw (IO.userError label)

private def tableCase (label : String) (layout : AirLayout) (point : List E)
    (tokens : List CallerToken) (accept : Bool) : IO Unit := do
  let counted := PCSBCSCallerParserCost.receiveTable layout point tokens
  let source := WHIRCallerClaims.receiveTable layout point tokens
  require (label++": source erasure") (counted.result == source)
  require (label++": acceptance") (counted.result.isSome == accept)
  let size := PCSBCSCallerParserCost.airLayoutSize layout+point.length
  require (label++": polynomial work") (counted.work ≤ 100*(size+1)^3)
  require (label++": literal traversal bound")
    (counted.work ≤ PCSBCSCallerParserCost.receiveTableWork layout point)
  if let some (table,_) := counted.result then
    require (label++": point length") (table.point.length == layout.tau)
    require (label++": eval length") (table.evals.length == layout.columns-layout.publicColumns)
    require (label++": slice length") (table.slices.length == (layout.fields.map BitField.width).sum)

private def constraintCase (label : String) (layouts : List AirLayout) (point : List E)
    (tokens : List CallerToken) (accept : Bool) : IO Unit := do
  let counted := PCSBCSCallerParserCost.constraintClaims layouts point tokens
  require (label++": source erasure") (counted.result == WHIRCallerClaims.constraintClaims layouts point tokens)
  require (label++": acceptance") (counted.result.isSome == accept)
  let size := PCSBCSCallerParserCost.airLayoutsSize layouts+point.length
  require (label++": polynomial work")
    (counted.work ≤ 100*(size+1)^3*size+2*size*size+50*size+20)
  if let some (tables,_) := counted.result then
    require (label++": table count") (tables.length == layouts.length)

private def busCase (label : String) (layout : BusLayout)
    (tokens : List CallerToken) (accept : Bool) : IO Unit := do
  let counted := PCSBCSCallerParserCost.busClaims layout tokens
  require (label++": source erasure") (counted.result == WHIRCallerClaims.busClaims layout tokens)
  require (label++": acceptance") (counted.result.isSome == accept)
  let size := PCSBCSCallerParserCost.busLayoutSize layout
  require (label++": logarithmic magnitude") (layout.mu ≤ size)
  require (label++": polynomial work") (counted.work ≤ PCSBCSCallerParserCost.busClaimsWork size)
  if let some ((point,claims),_) := counted.result then
    require (label++": GKR point length") (point.length == layout.mu)
    require (label++": claim count") (claims.length ≤ 2*size*size)
    require (label++": claim point lengths") (claims.all (fun c => c.point.length ≤ layout.mu))

private def zeroBus : List CallerToken :=
  List.replicate 5 (.draw 0) ++ [.sent 0,.draw 0]
private def oddBus : List CallerToken :=
  zeroBus ++ List.replicate 4 (.sent 0) ++ [.draw 1,.draw 0]
private def evenBus : List CallerToken :=
  zeroBus ++ List.replicate 8 (.sent 0) ++ [.draw 1,.draw 0,.draw 0]
private def nestedBus : List CallerToken :=
  oddBus ++ List.replicate 4 (.sent 0) ++ [.draw 1] ++
    List.replicate 8 (.sent 0) ++ [.draw 0,.draw 1,.draw 0]

def smoke : IO Unit := do
  tableCase "ordinary" ⟨1,2,0,[]⟩ [1] [.sent (E.ofK 2),.sent (E.ofK 3)] true
  tableCase "selected bits" ⟨1,3,1,[⟨1,2⟩]⟩ [1] [.sent (E.ofK 2),.sent 1,.sent 0] true
  tableCase "nonzero offset" ⟨0,2,0,[⟨1,2⟩,⟨0,1⟩]⟩ [] [.sent 1,.sent 0,.sent 1] true
  require "selected bit offsets and basis values"
    ((PCSBCSCallerParserCost.receiveTable ⟨0,2,0,[⟨1,2⟩,⟨0,1⟩]⟩ []
      [.sent 1,.sent 0,.sent 1]).result ==
      some (⟨[],[1,1],[1,0,1]⟩,[]))
  tableCase "zero width" ⟨0,1,0,[⟨0,0⟩]⟩ [] [] true
  tableCase "empty table" ⟨0,0,0,[]⟩ [] [] true
  tableCase "invalid public columns" ⟨0,0,1,[]⟩ [] [] false
  tableCase "invalid tau" ⟨2,0,0,[]⟩ [0] [] false
  tableCase "invalid field column" ⟨0,1,0,[⟨1,1⟩]⟩ [] [] false
  tableCase "invalid field width" ⟨0,1,0,[⟨0,65⟩]⟩ [] [] false
  tableCase "duplicate fields" ⟨0,2,0,[⟨0,1⟩,⟨0,1⟩]⟩ [] [] false
  tableCase "truncated cursor input" ⟨0,2,0,[]⟩ [] [.sent 1] false
  tableCase "truncated slices" ⟨0,1,0,[⟨0,2⟩]⟩ [] [.sent 1] false
  tableCase "wrong token kind" ⟨0,1,0,[]⟩ [] [.draw 1] false
  constraintCase "empty constraints" [] [] [] true
  constraintCase "constraint rounds and tables" [⟨1,1,0,[]⟩,⟨0,1,0,[⟨0,1⟩]⟩]
    [0] [.sent 0,.sent 0,.sent 0,.draw 1,.sent (E.ofK 2),.sent 1] true
  constraintCase "constraint point guard" [⟨1,0,0,[]⟩] [] [] false
  constraintCase "constraint truncated round" [⟨1,0,0,[]⟩] [0] [.sent 0] false
  constraintCase "constraint rejected table" [⟨0,1,0,[⟨0,65⟩]⟩] [] [] false
  busCase "empty bus" ⟨[],[],[],0⟩ zeroBus true
  busCase "duplicate bus coordinates" ⟨[⟨0,false,[.column 4,.column 4,.publicValue]⟩],[],[],0⟩
    (zeroBus++[.sent (E.ofK 2)]) true
  busCase "owned table skipped" ⟨[⟨0,true,[.tableExpression]⟩],[],[],0⟩ zeroBus true
  busCase "invalid expression" ⟨[⟨0,false,[.tableExpression]⟩],[],[],0⟩ zeroBus false
  busCase "odd bus point" ⟨[⟨1,false,[.column 4]⟩],[],[],0⟩ (oddBus++[.sent (E.ofK 2)]) true
  busCase "even bus point" ⟨[⟨2,false,[.column 4]⟩],[],[],0⟩ (evenBus++[.sent 1]) true
  busCase "nested bus point" ⟨[⟨3,false,[.column 4]⟩],[],[],0⟩ (nestedBus++[.sent 1]) true
  busCase "truncated nested bus" ⟨[⟨3,false,[.column 4]⟩],[],[],0⟩ oddBus false
  busCase "valid nonce" ⟨[],[],[],3⟩
    (.nonce 3 (ByteCodec.encodeNat 24 0)::zeroBus) true
  busCase "bad nonce" ⟨[],[],[],3⟩ [.nonce 2 (ByteCodec.encodeNat 24 0)] false
  busCase "missing claim" ⟨[⟨0,false,[.column 4]⟩],[],[],0⟩ zeroBus false
  IO.println "Counted/source bus and table polynomial smoke passed (29 accepted/rejected fixtures)."

end Whir.PCSBCSCallerBusTablePolynomialBoundSmoke

def main : IO Unit := Whir.PCSBCSCallerBusTablePolynomialBoundSmoke.smoke
