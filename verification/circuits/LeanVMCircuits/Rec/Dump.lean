module

public import LeanVMCircuits.Rec.Builder

@[expose] public section

/-!
The text of a builder dump (`cargo leanvm circuits`): one call per line, read as a `Model.Call`.

`CheckRec` and `CheckBind` both read dumps through `Dump.parse`.
-/

namespace LeanVMCircuits.Rec.Dump

open Model

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
  | "k_to_d" => return .kToD (← n 0) (← n 1) (← n 2) (← n 3)
  | "d_to_halves" => return .dToHalves (← n 0)
  | "compress" => return .compress (← n 0) (← n 1) (← n 2)
  | "node" => return .node (← n 0) (← n 1)
  | "parent" => return .parent (← n 0) (← n 1)
  | "leaf_block" =>
    let m ← nats (args.drop 1 |>.take 8)
    return .leafBlock (← n 0) m (← n 9) ((← n 10) = 1)
  | "block" =>
    let m ← nats (args.drop 1 |>.take 8)
    return .hashBlock (← n 0) m (← n 9)
  | "chain" => return .chain (← list args)
  | op => .error s!"unknown call: {op}"

/-- A line of a dump: a call, or a mark around the calls of one union pool or product (`Builder::mark`). -/
inductive Line where
  | call (c : Call)
  /-- `union::PoolShape::rows` of `chunks` chunks reading `digests` follows, up to `stop`. -/
  | pool (chunks : ℕ) (selecting : Bool) (digests : List ℕ)
  /-- `union::product` over the pool whose first item's first word is `first`, at `x1` and `weights`, up to `stop`. -/
  | product (first x1 : ℕ) (weights : List ℕ)
  | stop

def parseLine (line : String) : Except String Line := do
  let ws := line.splitOn " "
  match ws with
  | "pool" :: chunks :: selecting :: rest => return .pool (← nat chunks) ((← nat selecting) = 1) (← list rest)
  | "product" :: first :: x1 :: weights =>
    let w ← nats weights
    if w.length = 16 then return .product (← nat first) (← nat x1) w else .error "sixteen weights"
  | ["end", "pool"] | ["end", "product"] => pure .stop
  | _ => return .call (← parse line)

/-- Whether a line is one of the edge marks `CheckEdges` reads (`edge ...`): neither a call nor a block mark. -/
def isEdge (line : String) : Bool := line.startsWith "edge "

/-- Whether a line is one of the bus block marks `CheckBind` reads (`bus side ...`, `bus block ...`,
`BusBlocks::mark_lines`, `Bind.busGroups`). -/
def isBus (line : String) : Bool := line.startsWith "bus "

/-- A dump's calls, its circuit and its bus links, split at the `circuit` and `next` lines. The edge and bus marks are left out of the calls (`edgeLines` and `Bind.busGroups` read them). -/
def sections (text : String) : Except String (List String × String × String) := do
  let [head, rest] := text.splitOn "circuit\n" | .error "not one circuit"
  let [dumped, dumpedNext] := rest.splitOn "next\n" | .error "not one list of bus links"
  pure (head.splitOn "\n" |>.filter (fun l => l ≠ "" && !isEdge l && !isBus l), dumped, dumpedNext)

/-- A dump's edge marks, each without its `edge ` prefix, as words. -/
def edgeLines (text : String) : List (List String) :=
  ((text.splitOn "circuit\n").headD "").splitOn "\n" |>.filter isEdge |>.map fun l => (l.drop 5).toString.splitOn " "

end LeanVMCircuits.Rec.Dump
