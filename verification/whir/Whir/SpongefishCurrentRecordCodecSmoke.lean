import Whir.SpongefishCurrentRecordDecoder

/-! Literal current-codec boundary regression. This exercises the checked
hand-port, not Rust acceptance, read poisoning or cryptographic binding. -/
open Whir Whir.Concrete Whir.FiatShamirGame Whir.SpongefishSessionAdapter
open Whir.SpongefishCurrentRecordDecoder

private def changeByte (source : List Byte) (offset : Nat) (value : Byte) : List Byte :=
  source.zipIdx |>.map fun (b,i) => if i = offset then value else b

def main : IO Unit := do
  for n in [:65] do
    for first in [false,true] do
      let pending : List Byte := (List.range n).map fun i => ⟨(i+11)%256,Nat.mod_lt _ (by decide)⟩
      let r : Record := {
        shape := ⟨2,1,1,1⟩,root := fun i=>⟨i.val+1,by omega⟩,
        context := ⟨DuplexRefinement.zeroDigest,pending,first,13,7⟩,
        point := [E.ofK 1,E.ofK 2],value := E.ofK 3 }
      let bytes := openingBytes r
      let some (actual,rest) := decode r.shape (bytes ++ [99])
        | throw (IO.userError s!"valid saved context rejected at {n}/{first}")
      unless openingBytes actual = bytes && actual.context.pending = pending && rest = [99] do
        throw (IO.userError s!"literal current context changed at {n}/{first}")
      let candidates := suffixCandidates r.shape ([23,99,33] ++ bytes)
      unless candidates.length ≤ 4 && candidates.any (fun candidate => openingBytes candidate = bytes) do
        throw (IO.userError s!"current suffix lost the actual record at {n}/{first}")
      unless (decode r.shape (bytes.take (bytes.length-1))).isNone do
        throw (IO.userError "truncated literal record accepted")
      unless (decode r.shape (changeByte bytes 144 2)).isNone do
        throw (IO.userError "noncanonical first flag accepted")
      unless (decode r.shape (changeByte bytes 168 1)).isNone do
        throw (IO.userError "noncanonical squeezed high word accepted")
      if n % 24 ≠ 0 then
        unless (decode r.shape (changeByte bytes (184+n) 1)).isNone do
          throw (IO.userError s!"nonzero pending padding accepted at {n}")
  IO.println "PASS current raw32 record decoder: every pending length 0..64, both first flags, exact point/value and transport suffix, truncation, metadata normalization and zero byte-padding rejection"
  (← IO.getStdout).flush
