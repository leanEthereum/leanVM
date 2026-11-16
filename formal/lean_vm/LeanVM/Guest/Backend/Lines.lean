/-
  LeanVM.Guest.Backend.Lines

  The source line of every instruction the back end compiles: debug data, beside the compiler
  and proved of nothing.
-/

module

public import LeanVM.Guest.Backend.Compile
public import LeanVM.Guest.Backend.Text

/-!
# Source lines

The Rust compiler gives every instruction the line of the statement being lowered when it is
emitted (`cur_line`, `lower.rs`; `CompiledProgram::src_lines`), so a failed `assert` names its
line. The back end's passes carry no lines, and adding them would change the definitions its
proofs and its kernel-checked pieces are about, so the lines come from a pass of their own.

* The traced expansion records, with each statement it begins (`stmtKind`, where the Rust
  `stmt` sets `cur_line`), the length of the trace so far (`ExpandTrace.expandProgramLines`): so
  each event of the trace has a line, that of the statement begun last before it.
* `placeBlockL` walks a function as `Place.placeBlock` does, calling Place's own steps for
  everything but the statements that hold blocks (a branch, a `match`), whose walks it repeats,
  and gives each placed statement the line of an event (`LTree`): a statement the line of its
  `emit`, a branch's or a `match`'s head that of its first `enter`, an `else` jump or an arm's
  exit that of the `leave` before it, what `flush` places that of its event. Placement passes
  the events one at a time (`flush` and `expect` only), so the walk keeps the lines of those
  ahead beside it.
* `blockLines` lays the lines out as `Emit` lays out the instructions.

`compileLines` checks that this walk placed every function as `Backend.compile` did, by the text
of the two programs, so a change to `Place` that the walk does not follow fails there.
-/

namespace LeanVM.Guest.Backend.Lines

open LeanVM.Guest.Core LeanVM.Guest.Backend

@[expose] public section

/-- The source lines of a placed statement's instructions. -/
inductive LTree where
  /-- Every instruction on one line. -/
  | flat (line : Nat)
  /-- A branch: its head, its first block, its `else` jump, its second block. -/
  | ite (head : Nat) (zero : List LTree) (els : Nat) (nonzero : List LTree)
  /-- A chain of `match`es: its head, then each arm of each stage, its exit included. -/
  | chain (head : Nat) (stages : List (List (List LTree)))
  deriving Inhabited

/-- The line of each trace position `0..n`: the line of the statement begun last at or before
it, `0` before the first. `marks` are `(position, line)` in order. -/
def lineTable (marks : Array (Nat × Nat)) (n : Nat) : Array Nat := Id.run do
  let mut out := Array.emptyWithCapacity (n + 1)
  let mut i := 0
  let mut cur := 0
  for p in [0:n + 1] do
    while i < marks.size && (marks[i]!).1 ≤ p do
      cur := (marks[i]!).2
      i := i + 1
    out := out.push cur
  return out

/-- The walk with the lines of the events it has yet to pass, and the line of the last it passed. -/
abbrev L := StateT (List Nat × Nat) P

/-- The line of the event the walk is at (`back := 0`), or of the one it passed last. -/
def lineHere (back : Nat := 0) : L Nat := do
  let (ahead, last) ← getThe (List Nat × Nat)
  return if back == 0 then ahead.headD last else last

/-- One event passed. -/
def passed : L Unit :=
  modifyThe (List Nat × Nat) fun (ahead, last) => (ahead.tail, ahead.headD last)

/-- `expect`, passing the event. -/
def expectL (e : Event → Bool) (what : String) : L Unit := do
  expect e what
  passed

/-- How many statements the block holds so far. -/
def placedCount : L Nat := do
  return (← getThe St).out.size

/-- `m`, each statement it places on the line `line`. -/
def tracked (line : Nat) (m : L Unit) (acc : Array LTree) : L (Array LTree) := do
  let n0 ← placedCount
  m
  return acc ++ Array.replicate ((← placedCount) - n0) (.flat line)

/-- The events `flush` takes. -/
def isFlushed : Event → Bool
  | .alloc .. | .use _ | .shift .. | .chain | .note _ => true
  | _ => false

/-- `flush`, one event at a time, what each places on its line. -/
def flushL (upcoming : List Stmt) (acc : Array LTree) : L (Array LTree) := do
  let mut acc := acc
  for _ in [0:(← readThe Ctx).fuel] do
    match ← peek with
    | some e =>
        if isFlushed e then
          acc ← tracked (← lineHere) (do flushN upcoming 1; passed) acc
        else break
    | none => break
  return acc

/-- `inBlock` of a walk that returns its lines. -/
def inBlockL (m : L (Array LTree)) : L (List PStmt × List LTree) := do
  expectL isEnter "a block"
  let st ← getThe St
  let (out, scope) := (st.out, st.scope)
  modifyThe St fun s => { s with out := {} }
  let acc ← m
  let acc ← flushL [] acc
  let atLeave ← lineHere
  expectL isLeave "the end of a block"
  let acc ← if !(← getThe St).pending.isEmpty then
      tracked atLeave (do let o ← fresh; emitOp (.set o (.const 0 0))) acc
    else pure acc
  let inner := (← getThe St).out
  modifyThe St fun s => { s with out, scope }
  return (inner.toList, acc.toList)

mutual
/-- `placeBlock`, with the lines of what it places. -/
def placeBlockL : List Stmt → Array LTree → L (Array LTree)
  | [], acc => pure acc
  | s :: rest, acc => do
      let acc ← placeStmtL s rest acc
      endStmt
      placeBlockL rest acc

/-- `placeStmt`, with the lines of what it places onto `acc`, the block's so far. -/
def placeStmtL : Stmt → List Stmt → Array LTree → L (Array LTree)
  | .ite c z nz, _, acc => do
      let acc ← flushL [] acc
      let head ← lineHere
      let n0 ← placedCount
      let lc ← cellOf c
      let sfp ← selfFp
      let one ← oneCell
      let bdest ← fresh
      let hints ← takeHints
      let acc := acc ++ Array.replicate ((← placedCount) - n0) (.flat head)
      let (zeroBlk, zt) ← inBlockL (placeBlockL z #[])
      let els ← lineHere 1
      match ← peek with
      | some .enter =>
          let edest ← fresh
          let (nonzero, nt) ← inBlockL (placeBlockL nz #[])
          expectL isEmit "a branch"
          push (.ite hints lc bdest sfp zeroBlk true edest one nonzero)
          return acc.push (.ite head zt els nt)
      | _ =>
          if !nz.isEmpty then failP "an else block the trace does not enter"
          expectL isEmit "a branch"
          push (.ite hints lc bdest sfp zeroBlk false 0 0 [])
          return acc.push (.ite head zt els [])
  | .match_ x arms, rest, acc => do
      let acc ← flushL [] acc
      let st ← getThe St
      modifyThe St fun s => { s with chainIn := none, chain := false }
      let (entered, chained) := (st.chainIn, st.chain)
      let head ← lineHere
      let n0 ← placedCount
      let (lx, nextSel, sfp, one) ← matchCells x rest chained
      let (join, first, top) ← match entered with
        | some (first, join) => pure (join, first, none)
        | none => do
            let join ← fresh
            let hints ← takeHints
            let first ← allocTable arms.length
            let entry ← fresh
            pure (join, first, some (hints, entry))
      let exit ← match nextSel with
        | some (x', n') => do pure (ArmExit.next x' (← allocTable n') one sfp)
        | none => pure (ArmExit.join join one sfp)
      let acc := acc ++ Array.replicate ((← placedCount) - n0) (.flat head)
      let base := (← getThe St).next
      let (blocks, trees) ← placeArmsL arms 0 arms.length base exit
      expectL isEmit "a match"
      let acc ← match top with
        | some (hints, entry) => do
            push (.chain hints join lx entry one sfp [first] [blocks])
            pure (acc.push (.chain head [trees]))
        | none => do
            let out := (← getThe St).out
            match out.back?, acc.back? with
            | some (.chain h j x e o s firsts stages), some (.chain th tstages) =>
                let node := PStmt.chain h j x e o s (firsts ++ [first]) (stages ++ [blocks])
                modifyThe St fun st => { st with out := out.pop.push node }
                pure (acc.pop.push (.chain th (tstages ++ [trees])))
            | _, _ => failP "a chained match follows no match"
      match exit with
      | .next _ nf _ _ => modifyThe St fun s => { s with chainIn := some (nf, join) }
      | .join .. => pure ()
      return acc
  | s, rest, acc => do
      let acc ← flushL (s :: rest) acc
      -- `placeStmt` passes the statement's `emit` and no other event.
      tracked (← lineHere) (do placeStmt s rest; passed) acc

/-- `placeArms`, with each arm's lines, its exit on the line of the arm's end. -/
def placeArmsL : List (List Stmt) → Nat → Nat → Cell → ArmExit →
    L (List (List PStmt) × List (List LTree))
  | [], _, _, base, _ => do
      modifyThe St fun s => { s with next := base }
      pure ([], [])
  | arm :: more, j, n, base, exit => do
      modifyThe St fun s => { s with next := base }
      let (blk, bt) ← inBlockL (placeBlockL arm #[])
      let atEnd ← lineHere 1
      let leave ← match exit with
        | .next x first one sfp => do
            let e ← fresh
            pure [PStmt.op [] (.slot x first e), .op [] (.jump one e sfp)]
        | .join join one sfp =>
            pure (if j + 1 != n then [PStmt.op [] (.jump one join sfp)] else [])
      let top := (← getThe St).next
      let (blocks, trees) ← placeArmsL more (j + 1) n base exit
      modifyThe St fun s => { s with next := max s.next top }
      pure ((blk ++ leave) :: blocks, (bt ++ leave.map fun _ => .flat atEnd) :: trees)
end

/-- `placeBody`, with the lines of the function's statements. -/
def placeBodyL (tf : TracedFn) : L (List LTree) := do
  tf.core.params.zipIdx.forM fun (v, k) => bindTo v (.cell (2 + k))
  let acc ← placeBlockL tf.core.body #[]
  let acc ← flushL [] acc
  if !(← getThe St).rest.isEmpty then failP "the trace goes on past the function"
  return acc.toList

/-- `placeFn`, with the lines of the function's statements. -/
def placeFnL (loops : Loops) (sigs : SMap (Nat × Nat)) (tables : Tables) (tf : TracedFn)
    (marks : Array (Nat × Nat)) : Except String (PFn × List LTree × Tables) :=
  let lines := (lineTable marks tf.trace.size).toList
  match (placeBodyL tf).run (lines, 0) (ctxOf loops sigs tf) (initSt loops tables tf) with
  | .error e => .error e
  | .ok ((trees, _), st) =>
      .ok ({ name := tf.core.name, body := st.out.toList, frameSize := st.next }, trees, st.tables)

mutual
/-- The lines of a placed statement's instructions, as `emitStmt` lays them out. -/
def stmtLines : PStmt → LTree → Array Nat → Array Nat
  | .ite _ _ _ _ zero hasElse _ _ nonzero, .ite h zt e nt, acc =>
      let acc := blockLines zero zt ((acc.push h).push h)
      if hasElse then blockLines nonzero nt ((acc.push e).push e) else acc
  | .chain _ _ _ _ _ _ _ stages, .chain h ts, acc =>
      stagesLines stages ts (((acc.push h).push h).push h)
  | p, .flat l, acc => acc ++ Array.replicate (stmtSize p) l
  | p, _, acc => acc ++ Array.replicate (stmtSize p) 0

def blockLines : List PStmt → List LTree → Array Nat → Array Nat
  | [], _, acc => acc
  | p :: ps, t :: ts, acc => blockLines ps ts (stmtLines p t acc)
  | p :: ps, [], acc => blockLines ps [] (acc ++ Array.replicate (stmtSize p) 0)

def armsLines : List (List PStmt) → List (List LTree) → Array Nat → Array Nat
  | [], _, acc => acc
  | a :: as, t :: ts, acc => armsLines as ts (blockLines a t acc)
  | a :: as, [], acc => armsLines as [] (blockLines a [] acc)

def stagesLines : List (List (List PStmt)) → List (List (List LTree)) → Array Nat → Array Nat
  | [], _, acc => acc
  | s :: ss, t :: ts, acc => stagesLines ss ts (armsLines s t acc)
  | s :: ss, [], acc => stagesLines ss [] (armsLines s [] acc)
end

/-- The functions placed in order, each with the lines of its instructions (`placeFns`). -/
def placeFnsL (loops : Loops) (sigs : SMap (Nat × Nat)) :
    List (TracedFn × Array (Nat × Nat)) → Tables →
    Except String (List (Placed × Array Nat) × Tables)
  | [], tables => .ok ([], tables)
  | (tf, marks) :: rest, tables => do
      let (fn, trees, tables) ← placeFnL loops sigs tables tf marks
      let lines := blockLines fn.body trees #[]
      let code := (emitFn fn).1.code
      if lines.size != code.size then
        throw s!"in {fn.name}: {lines.size} lines for {code.size} instructions"
      let (pfs, tables) ← placeFnsL loops sigs rest tables
      return ((⟨fn, {}⟩, lines) :: pfs, tables)

/-- The program `Backend.compile` compiles and the source line of each of its instructions before
the padding, `0` for the jump tables. Fails when the walk here placed a function otherwise than
`Backend.compile`. -/
def compileLines (p : Source.Program) : Except String (Assembled × Array Nat) := do
  let c ← Backend.compile p
  let fns ← ExpandTrace.expandProgramLines p
  let traced := fns.map (·.1)
  let (placed, tables) ← placeFnsL (loopTable traced) (sigTable traced) fns {}
  let pfs := placed.map (·.1)
  let slots := tableSlots tables.len (fillsOf pfs).toArray tables.entries
  let ours := assemble (pfs.map fun pf => (emitFn pf.fn).1) slots
  if render ours != render c then
    throw "the line pass placed the program otherwise than the back end"
  let byName : SMap (Array Nat) := placed.foldl (init := {}) fun m (pf, ls) => m.insert pf.fn.name ls
  let lines := c.fns.foldl (init := #[]) fun acc (name, _, len) =>
    acc ++ (byName[name]?).getD (Array.replicate len 0)
  return (c, lines)

end
end LeanVM.Guest.Backend.Lines
