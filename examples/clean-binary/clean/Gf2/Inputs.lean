module

public import Lean.Data.Json

/-!
Parsing of `inputs.json`: `{"instances": [{"h": [8 words], "m": [16 words]}, ...]}`, each word an
8-hex-digit string.
-/

@[expose] public section

namespace Gf2.Inputs
open Lean (Json)

structure Instance where
  h : Array UInt32
  m : Array UInt32

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def word? (path : String) (j : Json) : Except String UInt32 := do
  let .str s := j | throw s!"{path}: expected a string"
  unless s.length == 8 do throw s!"{path}: \"{s}\" is not 8 hex digits"
  let n ← s.foldl (fun acc c => do
    let some d := hexDigit? c | throw s!"{path}: \"{s}\" is not 8 hex digits"
    return 16 * (← acc) + d) (pure 0)
  return n.toUInt32

def key? (path : String) (j : Json) (k : String) : Except String Json :=
  (j.getObjVal? k).mapError fun _ => s!"{path}: missing key \"{k}\""

def array? (path : String) (j : Json) : Except String (Array Json) :=
  (j.getArr?).mapError fun _ => s!"{path}: expected an array"

def words? (path : String) (len : Nat) (j : Json) : Except String (Array UInt32) := do
  let xs ← array? path j
  unless xs.size == len do throw s!"{path}: expected {len} words, got {xs.size}"
  xs.mapIdxM fun i x => word? s!"{path}[{i}]" x

def parse (text : String) : Except String (Array Instance) := do
  let j ← Json.parse text
  let instances ← array? "instances" (← key? "inputs" j "instances")
  if instances.isEmpty then throw "instances: empty"
  instances.mapIdxM fun i x => do
    let path := s!"instances[{i}]"
    return { h := ← words? s!"{path}.h" 8 (← key? path x "h"), m := ← words? s!"{path}.m" 16 (← key? path x "m") }

end Gf2.Inputs
