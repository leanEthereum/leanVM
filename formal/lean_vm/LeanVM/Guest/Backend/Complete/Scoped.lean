/-
  LeanVM.Guest.Backend.Complete.Scoped

  The traced functions whose frames the completeness proof can fill: every value a statement
  names was made on the statement's own path, in a block around it.
-/

module

public import LeanVM.Guest.Backend.Place
public import LeanVM.Guest.Memory.Fresh

/-!
# Scoped traces

Placement rewinds the next free cell for each arm of a `match` (the arms share their cells, one
arm running) and keeps every value it placed. It never checks that a value a statement names was
made on that statement's path, so it accepts a function whose frame no single memory can hold:

    match x [[v := 3], [w := 5]]; z := v · v; return

places `v` and `w` in one cell, and on the path through the second arm the cell must hold both
`σ w` and `σ v`. The completeness proof therefore asks of the traced function that it is
**scoped**: walking its body and its trace in the order placement reads them, every value a
statement names (`atomUses`, `atomTmps`, a branch condition, a selector, a call's arguments and
returns, the returned values) was made by an `alloc` event of a block around the statement on
its path, or is a parameter; every value a `use` or `shift` event names too; a path makes at
most one return area (`Kind.ret`), of at most the function's return cells; and no value placement
places lazily (`Kind.pooled`, `Kind.addr`) is made right before a block's start or end
(`flushEdge`), where the next statement placed is in another block.

`scopedE` is the walk, `scopedB` its decision and `Scoped` the proposition the proofs take. The
walk is placement's own reading of the trace (`flushN`, `expect`, `inBlock`, `placeArms`) with the
values in scope instead of cells.
-/

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The state of the walk: the trace from the event it is at, the values in scope on the path,
and whether the path made its return area. -/
structure SSt where
  rest : List Event
  live : VMap Unit
  retDone : Bool

/-- The values put in scope. -/
def addLive (live : VMap Unit) (vs : List V) : VMap Unit :=
  vs.foldl (fun m v => m.insert v ()) live

/-- The values made before the next statement or the end of the block (`flushN`): `rc` is the
function's return cells. -/
def flushS (rc : Nat) : List Event → VMap Unit → Bool → Except String SSt
  | [], live, r => .ok ⟨[], live, r⟩
  | e :: es, live, r =>
      match e with
      | .alloc vs kind =>
          if kind == .ret then
            if r then .error "a second return area on one path"
            else if rc < vs.length then .error "a return area past the return cells"
            else flushS rc es (addLive live vs) true
          else flushS rc es (addLive live vs) r
      | .use v =>
          if live.contains v then flushS rc es live r else .error "a use of a value out of scope"
      | .shift v _ =>
          if live.contains v then flushS rc es live r else .error "a shift of a value out of scope"
      | .chain => flushS rc es live r
      | .note _ => flushS rc es live r
      | _ => .ok ⟨e :: es, live, r⟩

/-- `flushS` at a state. -/
def flushAt (rc : Nat) (s : SSt) : Except String SSt := flushS rc s.rest s.live s.retDone

/-- Whether the events a flush passes (`flushS`) make no value placement places lazily, for the
statement after them (`Kind.pooled`, `Kind.addr`). -/
def lazyFree : List Event → Bool
  | [] => true
  | e :: es =>
      match e with
      | .alloc _ .pooled => false
      | .alloc _ .addr => false
      | .alloc _ _ | .use _ | .shift _ _ | .chain | .note _ => lazyFree es
      | _ => true

/-- `flushAt` before a block's start or end: no value made lazily waits past it, since the next
statement placed is in another block. -/
def flushEdge (rc : Nat) (s : SSt) : Except String SSt :=
  if lazyFree s.rest then flushAt rc s else .error "a value made lazily before a block's edge"

theorem flushEdge_ok {rc : Nat} {s s' : SSt} (h : flushEdge rc s = .ok s') :
    lazyFree s.rest = true ∧ flushAt rc s = .ok s' := by
  unfold flushEdge at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

/-- Pass the event `e`, which the walk must be at (`expect`). -/
def expectS (e : Event → Bool) (what : String) (s : SSt) : Except String SSt :=
  match s.rest with
  | ev :: es => if e ev then .ok { s with rest := es } else .error s!"the trace is not at {what}"
  | [] => .error s!"the trace ends before {what}"

/-- The values are in scope. -/
def inScope (live : VMap Unit) (vs : List V) : Bool := vs.all live.contains

/-- A statement's own values in scope, or the error naming the first that is not. -/
def needScope (live : VMap Unit) (vs : List V) (what : String) : Except String Unit :=
  if inScope live vs then .ok ()
  else .error s!"{what} names a value out of scope: {(vs.find? (!live.contains ·)).map (·.idx)}"

/-- The values a statement names itself, its blocks apart. -/
def ownUses : Stmt → List V
  | .atom a => atomUses a ++ atomTmps a
  | .ite c _ _ => [c]
  | .match_ x _ => [x]
  | .call _ args rets => args ++ rets
  | .callIf c _ args => c :: args
  | .dispatch x _ args rets => x :: (args ++ rets)
  | .ret vs => vs

/-- A block of its own (`inBlock`), its statements walked by `blk`: its values leave scope at its
end. -/
def scopeInner (rc : Nat) (blk : SSt → Except String SSt) (s : SSt) : Except String SSt :=
  match expectS isEnter "a block" s with
  | .error e => .error e
  | .ok s₁ =>
    match blk s₁ with
    | .error e => .error e
    | .ok s₂ =>
      match flushEdge rc s₂ with
      | .error e => .error e
      | .ok s₃ =>
        match expectS isLeave "the end of a block" s₃ with
        | .error e => .error e
        | .ok s₄ => .ok { s₄ with live := s.live }

/-- An address of no cells: placement binds it to a frame address no event ties to its value. -/
def noCells : Stmt → Bool
  | .atom (.frameAddr _ []) => true
  | _ => false

/-- A statement other than a branch or a `match`: its values in scope after the values made
before it; not an address of no cells. -/
def scopeFlat (rc : Nat) (st : Stmt) (s : SSt) : Except String SSt :=
  match flushAt rc s with
  | .error e => .error e
  | .ok s₁ =>
    match expectS isEmit "a statement" s₁ with
    | .error e => .error e
    | .ok s₂ =>
      match needScope s₂.live (ownUses st) "a statement" with
      | .error e => .error e
      | .ok () => if noCells st then .error "an address of no cells" else .ok s₂

/-- A branch after its blocks were walked: the `else` block, if the trace enters it, then the
branch's own event. `nz` walks the `else` block; `before` is whether the path had made its return
area before the branch. -/
def scopeIteTail (nzEmpty : Bool) (nz : SSt → Except String SSt) (before : Bool) (s₁ : SSt) :
    Except String SSt :=
  match s₁.rest with
  | .enter :: _ =>
    match nz { s₁ with retDone := before } with
    | .error e => .error e
    | .ok s₂ => expectS isEmit "a branch" { s₂ with retDone := s₁.retDone || s₂.retDone }
  | _ =>
    if !nzEmpty then .error "an else block the trace does not enter"
    else expectS isEmit "a branch" s₁

mutual
/-- A block. -/
def scopeBlock (rc : Nat) : List Stmt → SSt → Except String SSt
  | [], s => .ok s
  | st :: rest, s =>
    match scopeStmt rc st s with
    | .error e => .error e
    | .ok s' => scopeBlock rc rest s'

/-- A statement: its values in scope after the values made before it. -/
def scopeStmt (rc : Nat) : Stmt → SSt → Except String SSt
  | .ite c z nz, s =>
    match flushEdge rc s with
    | .error e => .error e
    | .ok s =>
      match needScope s.live [c] "a branch" with
      | .error e => .error e
      | .ok () =>
        match scopeInner rc (fun s' => scopeBlock rc z s') s with
        | .error e => .error e
        | .ok s₁ => scopeIteTail nz.isEmpty (scopeInner rc (fun s' => scopeBlock rc nz s'))
            s.retDone s₁
  | .match_ x arms, s =>
    match flushEdge rc s with
    | .error e => .error e
    | .ok s =>
      match needScope s.live [x] "a match" with
      | .error e => .error e
      | .ok () =>
        match scopeArms rc arms s s.retDone with
        | .error e => .error e
        | .ok s' => expectS isEmit "a match" s'
  | .atom a, s => scopeFlat rc (.atom a) s
  | .call f args rets, s => scopeFlat rc (.call f args rets) s
  | .callIf c f args, s => scopeFlat rc (.callIf c f args) s
  | .dispatch x fs args rets, s => scopeFlat rc (.dispatch x fs args rets) s
  | .ret vs, s => scopeFlat rc (.ret vs) s

/-- The arms of a `match`, each from the scope before it; `acc` is whether some arm walked so far
made the return area. -/
def scopeArms (rc : Nat) : List (List Stmt) → SSt → Bool → Except String SSt
  | [], s, acc => .ok { s with retDone := acc }
  | arm :: more, s, acc =>
    match scopeInner rc (fun s' => scopeBlock rc arm s') s with
    | .error e => .error e
    | .ok s₁ => scopeArms rc more { s₁ with retDone := s.retDone } (acc || s₁.retDone)
end

/-- The values the events make. -/
def allocsOf (rs : List Event) : List V :=
  rs.flatMap fun
    | .alloc vs _ => vs
    | _ => []

/-- Whether the values `vs` are distinct and none is in `seen`. -/
def onceAfter : VMap Unit → List V → Bool
  | _, [] => true
  | seen, v :: vs => !seen.contains v && onceAfter (seen.insert v ()) vs

/-- Whether the trace makes each value once and makes no parameter (placement places a value
once). -/
def allocsOnceB (tf : TracedFn) : Bool :=
  onceAfter (addLive {} tf.core.params) (allocsOf tf.trace.toList)

/-- The walk of a traced function: its values made once, its parameters in scope, its body, the
values made after its last statement, and nothing left of the trace. -/
def scopedE (tf : TracedFn) : Except String Unit :=
  if !allocsOnceB tf then .error "a value made twice, or a parameter made" else
  match scopeBlock tf.rets tf.core.body ⟨tf.trace.toList, addLive {} tf.core.params, false⟩ with
  | .error e => .error e
  | .ok s =>
    match flushAt tf.rets s with
    | .error e => .error e
    | .ok s => if s.rest.isEmpty then .ok () else .error "the trace goes on past the function"

/-- **Scoped, decided.** -/
def scopedB (tf : TracedFn) : Bool :=
  match scopedE tf with
  | .ok () => true
  | .error _ => false

/-- **A scoped traced function**: what the completeness proof asks of each function beyond its
placement. -/
def Scoped (tf : TracedFn) : Prop := scopedB tf = true


/-! ## No direct self call -/

mutual
/-- Whether a statement calls `f` by a `call` or a `dispatch`, at any depth (a loop helper's
closing `callIf` is not counted). -/
def callsS (f : String) : Stmt → Bool
  | .call g _ _ => g == f
  | .dispatch _ gs _ _ => gs.contains f
  | .ite _ z n => callsL f z || callsL f n
  | .match_ _ arms => callsA f arms
  | _ => false

/-- `callsS` of a block. -/
def callsL (f : String) : List Stmt → Bool
  | [] => false
  | s :: ss => callsS f s || callsL f ss

/-- `callsS` of arms. -/
def callsA (f : String) : List (List Stmt) → Bool
  | [] => false
  | a :: as => callsL f a || callsA f as
end

/-- **No direct self call, decided**: the function calls itself by no `call` and no `dispatch`. -/
def noSelfCallB (tf : TracedFn) : Bool := !callsL tf.core.name tf.core.body

/-- **No direct self call**: a call of the function itself, other than a loop helper's closing
`callIf`, would write a return pc and this frame's pointer into a callee header that the frame
side gives this frame's own header. -/
def NoSelfCall (tf : TracedFn) : Prop := noSelfCallB tf = true

end
end LeanVM.Guest.Backend.Complete
