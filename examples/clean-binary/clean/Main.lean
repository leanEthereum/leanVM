module

public import Gf2.R1CS
public import Gf2.Inputs
-- Keeps the reference-vector checks in the executable's build.
public import Gf2.Check

@[expose] public section

open Gf2

def usage : String :=
  "usage: clean_export r1cs <out.r1cs>\n" ++
  "       clean_export witness <inputs.json> <out.bin>"

def orFail {α : Type} (context : String) : Except String α → IO α
  | .ok a => pure a
  | .error msg => throw (IO.userError s!"{context}: {msg}")

def main (args : List String) : IO Unit := do
  match args with
  | ["r1cs", out] =>
    let ex ← orFail "export" (R1CS.toCLB1 Blake2s.nPublic Blake2s.ops)
    IO.FS.writeBinFile out ex.body
    let s := ex.stats
    IO.println s!"{out}: {s.constraints} constraints, {s.signals} signals, \
      nnz A {s.nnzA}, B {s.nnzB}, C {s.nnzC}"
  | ["witness", inputs, out] =>
    let instances ← orFail s!"invalid {inputs}" (Inputs.parse (← IO.FS.readFile inputs))
    let ops := Blake2s.ops
    let signals := 1 + Operations.localLength ops
    IO.FS.withFile out .write fun h => do
      h.write (R1CS.witnessHeader signals instances.size)
      for x in instances do
        h.write (R1CS.packWitness (witgen (Blake2s.inputHint (Blake2s.inputBits x.h x.m)) ops))
    IO.println s!"{out}: {instances.size} instances, {signals} signals"
  | _ => throw (IO.userError usage)
