import LeanVMCircuits.Rec.Dump
import LeanVMCircuits.Rec.StmtFirst

/-!
`lake exe checkrec <dump>...`: replay each dump's builder calls (`cargo leanvm circuits`) through the Lean model of
the builder, finish the circuit as `Builder::finish` does, and check it is the circuit in the dump.
-/

open LeanVMCircuits.Rec.Model

namespace CheckRec

/-- The root of `x`'s class. -/
partial def find (parent : Array ℕ) (x : ℕ) : ℕ :=
  let p := parent[x]!
  if p = x then x else find parent p

/-- `Builder::finish`'s circuit as `Circuit::dump` prints it, and every slot's wire class, per table. -/
def finish (s : State) : String × List (List ℕ) := Id.run do
  -- `statement_first`: the statement's public rows first, in statement order, then the constants' (`pubFirst`, the
  -- order `stmtFirst` gives the child's circuit in the AIR link).
  let ordered := pubFirst s.pub.toList
  let pubRows := ordered.map (·.1)
  let pubs := ordered.map (·.2)
  -- Wire classes, numbered by their first slot.
  let mut parent := Array.range s.next
  for (a, b) in s.unions do
    let ra := find parent a
    let rb := find parent b
    if ra ≠ rb then parent := parent.set! rb ra
  let mut number : Array (Option ℕ) := Array.replicate s.next none
  let mut count := 0
  let mut out := ""
  let mut classes : List (List ℕ) := []
  let flat (rs : Array (List ℕ)) : List ℕ := rs.toList.flatten
  let tables := [flat s.emul, flat s.exk, flat s.hash, flat s.split, flat s.cast, pubRows]
  for t in tables do
    let mut line := s!"table {t.length}"
    let mut cs : Array ℕ := #[]
    for w in t do
      let r := find parent w
      let c ← match number[r]! with
        | some c => pure c
        | none => do
          number := number.set! r (some count)
          count := count + 1
          pure (count - 1)
      line := line ++ s!" {c}"
      cs := cs.push c
    out := out ++ line ++ "\n"
    classes := classes ++ [cs.toList]
  for p in pubs do
    out := out ++ (match p with
      | .const v => s!"const {" ".intercalate (v.map toString)}"
      | .statement i => s!"statement {i}") ++ "\n"
  (out ++ s!"statement_len {s.statement}\n", classes)

/-- `Rec.classNext` of every slot, as `FixedColumns::of` writes it: the `SlotKey` of the next slot of its class in
slot order, the class's first after its last, per table, row-major. -/
def nextKeys (classes : List (List ℕ)) : String := Id.run do
  let widths := [4, 4, 16, 65, 8, 1]
  let firsts := [0, 4, 8, 24, 89, 97]
  -- Every slot's key and class, in slot order.
  let mut slots : Array (ℕ × ℕ) := #[]
  for ((cs, n), first) in (classes.zip widths).zip firsts do
    for (c, i) in cs.zipIdx do
      slots := slots.push ((first + i % n) * 2 ^ 32 + i / n, c)
  let nClasses := slots.foldl (fun m p => max m (p.2 + 1)) 0
  let mut firstOf : Array (Option ℕ) := Array.replicate nClasses none
  let mut lastOf : Array (Option ℕ) := Array.replicate nClasses none
  let mut next : Array ℕ := Array.replicate slots.size 0
  for i in [0:slots.size] do
    let c := slots[i]!.2
    match lastOf[c]! with
    | some j => next := next.set! j slots[i]!.1
    | none => firstOf := firstOf.set! c (some i)
    lastOf := lastOf.set! c (some i)
  for c in [0:nClasses] do
    match lastOf[c]!, firstOf[c]! with
    | some j, some i => next := next.set! j slots[i]!.1
    | _, _ => pure ()
  let mut out := ""
  let mut pos := 0
  for cs in classes do
    let mut line := s!"table {cs.length}"
    for _ in cs do
      line := line ++ s!" {next[pos]!}"
      pos := pos + 1
    out := out ++ line ++ "\n"
  return out

def check (path : System.FilePath) : IO Bool := do
  let text ← IO.FS.readFile path
  let (calls, dumped, dumpedNext) ← match LeanVMCircuits.Rec.Dump.sections text with
    | .ok r => pure r
    | .error e => do IO.eprintln s!"{path}: {e}"; return false
  let mut s : State := {}
  for line in calls do
    match LeanVMCircuits.Rec.Dump.parseLine line with
    | .ok (.call call) =>
      -- The model's contracts hold of calls naming wires already made, of the sizes the Rust methods take.
      unless call.args.all (· < s.next) && call.ok do
        IO.eprintln s!"{path}: a call names a wire not yet made or has the wrong size: {line}"; return false
      s := (call.run.run s).2
    -- Marks group calls for `checkbind`; the calls are replayed one by one here.
    | .ok _ => pure ()
    | .error e => IO.eprintln s!"{path}: {e}"; return false
  let (built, classes) := finish s
  if built = dumped then
    if nextKeys classes ≠ dumpedNext then
      IO.eprintln s!"{path}: the bus's links are not each class's cycle in slot order"
      return false
    IO.println s!"{path}: {calls.length} calls, the model builds the same circuit, its bus links are its classes' cycles"
    return true
  else
    let bl := built.splitOn "\n"
    let dl := dumped.splitOn "\n"
    let i := (bl.zip dl).findIdx fun (a, b) => a ≠ b
    IO.eprintln s!"{path}: the model's circuit differs at line {i}"
    IO.eprintln s!"  model:  {(bl.getD i "").take 200}"
    IO.eprintln s!"  dumped: {(dl.getD i "").take 200}"
    return false

end CheckRec

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  for path in args do
    ok := (← CheckRec.check path) && ok
  return if ok then 0 else 1
