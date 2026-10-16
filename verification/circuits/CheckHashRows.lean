import LeanVMCircuits.Rec.HashRowsMap

/-!
`lake exe checkhashrows <dump>` checks `HashRows.rowsOf`, the model of `Hash::circuit`'s rows, against the rows Rust
builds, written as `hash-rows.dump` by the `circuits` CLI (`Hash::rows_dump`). Line `s` of the dump is row `s` of
`Circuit::row_values` at the column weights `w_j = (mix(3j), mix(3j + 1), mix(3j + 2))`, SplitMix64's outputs: `A_0 w`
then `B_0 w`, 192 bits each. A row's value is the XOR of its form's weights, so it is the form at 192 lanes at once. The
check evaluates `rowsOf` at the same weights, as 192-bit lanes under XOR, and requires every slot's pair to be the
dump's, an empty row's being zero. By `HashRows.rowsOf_map` these are the forms of `hashA0` and `hashB0` at the
weights, so a form the model gets wrong passes only where the weights of the columns it gets wrong sum to zero in all
192 lanes.
-/

open LeanVMCircuits.Rec

/-- 192 GF(2) lanes, added by XOR. -/
structure Lanes where
  bits : Nat
  deriving BEq

instance : Add Lanes := ⟨fun a b => ⟨a.bits ^^^ b.bits⟩⟩

/-- SplitMix64's output at counter `i + 1` (`mix` in `hash.rs`). -/
def mix (i : UInt64) : UInt64 :=
  let x := (i + 1) * 0x9E3779B97F4A7C15
  let x := (x ^^^ (x >>> 30)) * 0xBF58476D1CE4E5B9
  let x := (x ^^^ (x >>> 27)) * 0x94D049BB133111EB
  x ^^^ (x >>> 31)

/-- Column `j`'s weight: `c0 + 2^64 c1 + 2^128 c2`. -/
def weight (j : ℕ) : Lanes :=
  let j := (3 * j).toUInt64
  ⟨(mix j).toNat ||| (mix (j + 1)).toNat <<< 64 ||| (mix (j + 2)).toNat <<< 128⟩

/-- A field element's 48 hex digits, `c2` first. -/
def parseHex (s : String) : Option ℕ :=
  if s.length != 48 then none
  else s.foldl (fun acc c => acc.bind fun n =>
    if '0' ≤ c ∧ c ≤ '9' then some (16 * n + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (16 * n + (c.toNat - 'a'.toNat + 10))
    else none) (some 0)

def main (args : List String) : IO UInt32 := do
  let [path] := args
    | IO.eprintln "usage: checkhashrows <dump>"
      return 2
  let lines := (← IO.FS.lines path)
  let mut dump : Array (ℕ × ℕ) := Array.mkEmpty lines.size
  for line in lines, i in [0:lines.size] do
    match line.splitOn " " with
    | [a, b] =>
      match parseHex a, parseHex b with
      | some a, some b => dump := dump.push (a, b)
      | _, _ =>
        IO.eprintln s!"{path}: line {i + 1} is not two 48-digit hex values"
        return 1
    | _ =>
      IO.eprintln s!"{path}: line {i + 1} is not two values"
      return 1
  let rows := HashRows.rowsOf weight
  let mut model : Array (Option (ℕ × ℕ)) := Array.replicate dump.size none
  for (s, a, b) in rows do
    if h : s < model.size then
      if model[s].isSome then
        IO.eprintln s!"{path}: the model has two rows at slot {s}"
        return 1
      model := model.set s (some (a.bits, b.bits))
    else
      IO.eprintln s!"{path}: the model's row at slot {s} is past the dump's {dump.size} slots"
      return 1
  for i in [0:dump.size] do
    let want := (model[i]!).getD (0, 0)
    if dump[i]! != want then
      let hex (p : ℕ × ℕ) := s!"{String.ofList (Nat.toDigits 16 p.1)} {String.ofList (Nat.toDigits 16 p.2)}"
      IO.eprintln s!"{path}: slot {i} is `{hex dump[i]!}`, the model's is `{hex want}`"
      return 1
  IO.println s!"{path}: the {dump.size} slots' rows are the model's ({rows.length} rows)"
  return 0
