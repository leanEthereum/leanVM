import LeanVMCircuits.Rec.Builder

/-!
`lake exe checkrec <dump>...`: replay each dump's builder calls (`cargo leanvm circuits`) through the Lean model of
the builder, finish the circuit as `Builder::finish` does, and check it is the circuit in the dump.
-/

open LeanVMCircuits.Rec.Model

namespace CheckRec

def nat (s : String) : Except String ℕ :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"not a number: {s}"

def nats (ws : List String) : Except String (List ℕ) := ws.mapM nat

/-- A list given as its length, then its numbers. -/
def list (ws : List String) : Except String (List ℕ) := do
  let n ← nat (ws.headD "")
  let xs ← nats ws.tail
  if xs.length = n then pure xs else .error "list length"

def parse (line : String) : Except String Call := do
  let ws := line.splitOn " "
  let args := ws.tail
  let n (i : ℕ) : Except String ℕ := nat (args.getD i "")
  match ws.headD "" with
  | "free_e" => pure .freeE
  | "free_k" => pure .freeK
  | "free_d" => pure .freeD
  | "eq_e" => return .eqE (← n 0) (← n 1)
  | "eq_k" => return .eqK (← n 0) (← n 1)
  | "eq_d" => return .eqD (← n 0) (← n 1)
  | "eq_e_const" => return .eqConstE (← n 0) (← n 1) (← n 2) (← n 3)
  | "eq_k_const" => return .eqConstK (← n 0) (← n 1)
  | "e_const" => return .eConst (← n 0) (← n 1) (← n 2)
  | "k_const" => return .kConst (← n 0)
  | "d_const" => return .dConst (← nats args)
  | "zero" => pure .zero
  | "one" => pure .one
  | "expose_e" => return .exposeE (← n 0)
  | "mul_add" => return .mulAdd (← n 0) (← n 1) (← n 2)
  | "mul" => return .mul (← n 0) (← n 1)
  | "add" => return .add (← n 0) (← n 1)
  | "square" => return .square (← n 0)
  | "mul_k_add" => return .mulKAdd (← n 0) (← n 1) (← n 2)
  | "mul_const_add" => return .mulConstAdd (← n 0) (← n 1) (← n 2) (← n 3) (← n 4)
  | "inv" => return .inv (← n 0)
  | "sum" => return .sum (← list args)
  | "split" => return .split (← n 0)
  | "pack" => return .pack (← list args)
  | "e_to_k" => return .eToK (← n 0)
  | "k_to_e" => return .kToE (← n 0) (← n 1) (← n 2)
  | "k_to_e1" => return .kToE1 (← n 0)
  | "d_to_k" => return .dToK (← n 0)
  | "d_to_e_and_k" => return .dToEAndK (← n 0)
  | "halves_to_d" => return .halvesToD (← n 0) (← n 1)
  | "compress" => return .compress (← n 0) (← n 1) (← n 2)
  | "node" => return .node (← n 0) (← n 1)
  | "parent" => return .parent (← n 0) (← n 1)
  | "leaf_block" =>
    let m ← nats (args.drop 1 |>.take 8)
    return .leafBlock (← n 0) m (← n 9) ((← n 10) = 1)
  | "chain" => return .chain (← list args)
  | op => .error s!"unknown call: {op}"

/-- The root of `x`'s class. -/
partial def find (parent : Array ℕ) (x : ℕ) : ℕ :=
  let p := parent[x]!
  if p = x then x else find parent p

/-- `Builder::finish`'s circuit as `Circuit::dump` prints it, and every slot's wire class, per table. -/
def finish (s : State) : String × List (List ℕ) := Id.run do
  -- `statement_first`: the statement's public rows first, in statement order, then the constants'.
  let rows := s.pub.toList
  let stmt := (rows.filterMap fun r => match r.2 with
    | .statement j => some (j, r)
    | .const _ => none).mergeSort (fun a b => a.1 ≤ b.1)
  let consts := rows.filter fun r => match r.2 with
    | .const _ => true
    | .statement _ => false
  let ordered := stmt.map (·.2) ++ consts
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
  let [head, rest] := text.splitOn "circuit\n" | do
    IO.eprintln s!"{path}: not one circuit"; return false
  let [dumped, dumpedNext] := rest.splitOn "next\n" | do
    IO.eprintln s!"{path}: not one list of bus links"; return false
  let calls := head.splitOn "\n" |>.filter (· ≠ "")
  let mut s : State := {}
  for line in calls do
    match parse line with
    | .ok call =>
      -- The model's contracts hold of calls naming wires already made, of the sizes the Rust methods take.
      unless call.args.all (· < s.next) && call.ok do
        IO.eprintln s!"{path}: a call names a wire not yet made or has the wrong size: {line}"; return false
      s := (call.run.run s).2
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
