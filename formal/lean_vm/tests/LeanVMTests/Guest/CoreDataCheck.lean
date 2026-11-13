import LeanVM.Guest.Data.Source
import LeanVM.Guest.Expand
import LeanVM.Guest.Code
import LeanVM.Guest.Renumber
import Statement.Data.Bytecode

/-!
# The core IR's data, checked

`coreProgram`'s definitions (`Guest/Data/Core.lean`, `Guest/Pack`, noncomputable) read back from
their elaborated terms, and compared with `(Expand.expandProgram Data.guest).map (·.map
Fn.renumber)`, both evaluated without the kernel: the data cannot drift from the source. And the
expansion against the compiled functions (`Data.functions`), `KECCAK` by `KECCAK`. Both are
`check`, compiled (`lake exe test-runs`, on the environment of `LeanVM.Guest.CoreData`'s `.olean`,
loaded when it runs). This module does not import the data, so the executable does not compile
it; `Guest/CoreData.lean` checks access to it.
-/

namespace LeanVMTests.Guest.CoreData

open Lean LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Core

/-- Reading a term back, its constants unfolded to their definitions. -/
abbrev R := ReaderT Environment (Except String)

def bad {α : Type} (what : String) (e : Expr) : R α :=
  throw s!"not {what}: {e.dbgToString.take 200}"

partial def unfold (e : Expr) : R Expr := do
  let e := e.consumeMData
  if let .const n _ := e then
    if let some (.defnInfo d) := (← read).find? n then return ← unfold d.value
  return e

def nat (e : Expr) : R Nat := do
  match (← unfold e) with
  | .lit (.natVal n) => return n
  | e@(.app ..) => match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => return n
    | _ => bad "a numeral" e
  | e => bad "a numeral" e

def str (e : Expr) : R String := do
  match (← unfold e) with
  | .lit (.strVal s) => return s
  | e => bad "a string" e

partial def list {α : Type} (f : Expr → R α) (e : Expr) : R (List α) := do
  let e ← unfold e
  match e.getAppFnArgs with
  | (``List.nil, #[_]) => return []
  | (``List.cons, #[_, h, t]) => return (← f h) :: (← list f t)
  | (``HAppend.hAppend, #[_, _, _, _, a, b]) => return (← list f a) ++ (← list f b)
  | _ => bad "a list" e

def app (e : Expr) : R (Name × Array Expr) := do
  return (← unfold e).getAppFnArgs

def seg (e : Expr) : R Seg := do
  match ← app e with
  | (``Seg.s, #[i]) => return .s (← nat i)
  | (``Seg.u, #[j]) => return .u (← nat j)
  | (``Seg.t, #[]) => return .t
  | (``Seg.e, #[]) => return .e
  | (``Seg.a, #[j]) => return .a (← nat j)
  | (``Seg.i, #[f, k]) => return .i (← str f) (← nat k)
  | _ => bad "a step" e

def val (e : Expr) : R V := do
  match ← app e with
  | (``V.mk, #[p, t, i]) => return ⟨← list seg p, ← nat t, ← nat i⟩
  | (``V.n, #[i]) => return .n (← nat i)
  | _ => bad "a value" e

def word' (e : Expr) : R E := do
  match e.consumeMData.getAppFnArgs with
  | (``word, #[a, b]) => return word (← nat a) (← nat b)
  | _ => bad "a word" e

def vals (e : Expr) : R (List V) := list val e

def bool (e : Expr) : R Bool := do
  match ← app e with
  | (``Bool.true, #[]) => return true
  | (``Bool.false, #[]) => return false
  | _ => bad "a Bool" e

def option {α : Type} (f : Expr → R α) (e : Expr) : R (Option α) := do
  match ← app e with
  | (``Option.none, #[_]) => return none
  | (``Option.some, #[_, a]) => return some (← f a)
  | _ => bad "an Option" e

def dest (e : Expr) : R Dest := do
  match ← app e with
  | (``Dest.stack, #[cs]) => return .stack (← vals cs)
  | (``Dest.heap, #[p, o, l]) => return .heap (← val p) (← nat o) (← nat l)
  | _ => bad "a destination" e

def hint (e : Expr) : R Hint := do
  match ← app e with
  | (``Hint.witness, #[s, d]) => return .witness (← str s) (← dest d)
  | (``Hint.bits, #[v, s, n, d]) => return .bits (← val v) (← nat s) (← nat n) (← dest d)
  | (``Hint.bitsExp, #[v, n, d]) => return .bitsExp (← val v) (← nat n) (← dest d)
  | (``Hint.digitsExp, #[v, n, k, b, s, c, d]) =>
      return .digitsExp (← val v) (← nat n) (← nat k) (← nat b) (← nat s) (← option val c) (← dest d)
  | (``Hint.windowsExp, #[v, s, w, k, d]) =>
      return .windowsExp (← val v) (← nat s) (← nat w) (← nat k) (← dest d)
  | (``Hint.limbs, #[v, d]) => return .limbs (← val v) (← vals d)
  | (``Hint.log2Ceil, #[b, n, f, d]) => return .log2Ceil (← dest b) (← nat n) (← nat f) (← val d)
  | (``Hint.inverse, #[x, d]) => return .inverse (← val x) (← val d)
  | (``Hint.alloc, #[d, n]) => return .alloc (← val d) (← nat n)
  | (``Hint.allocDyn, #[d, s]) => return .allocDyn (← val d) (← val s)
  | _ => bad "a hint" e

def atom (e : Expr) : R Atom := do
  match ← app e with
  | (``Atom.const, #[d, c]) => return .const (← val d) (← word' c)
  | (``Atom.add, #[d, a, b]) => return .add (← val d) (← val a) (← val b)
  | (``Atom.mul, #[d, a, b]) => return .mul (← val d) (← val a) (← val b)
  | (``Atom.copy, #[d, s]) => return .copy (← val d) (← val s)
  | (``Atom.load, #[d, p, o]) => return .load (← val d) (← val p) (← nat o)
  | (``Atom.assertEq, #[a, b]) => return .assertEq (← val a) (← val b)
  | (``Atom.assertNe, #[x, i, p]) => return .assertNe (← val x) (← val i) (← val p)
  | (``Atom.rangeCheck, #[x, y, t1, t2, k]) =>
      return .rangeCheck (← val x) (← val y) (← val t1) (← val t2) (← val k)
  | (``Atom.assertInK, #[a, b]) => return .assertInK (← val a) (← val b)
  | (``Atom.keccak, #[ins, outs, i, o]) =>
      return .keccak (← vals ins) (← vals outs) (← bool i) (← bool o)
  | (``Atom.frameAddr, #[p, r]) => return .frameAddr (← val p) (← vals r)
  | (``Atom.hint, #[h]) => return .hint (← hint h)
  | (``Atom.touch, #[t, p]) => return .touch (← val t) (← val p)
  | _ => bad "an atom" e

partial def stmt (e : Expr) : R Stmt := do
  match ← app e with
  | (``Stmt.atom, #[a]) => return .atom (← atom a)
  | (``Stmt.ite, #[c, z, n]) => return .ite (← val c) (← list stmt z) (← list stmt n)
  | (``Stmt.match_, #[x, as]) => return .match_ (← val x) (← list (list stmt) as)
  | (``Stmt.call, #[f, a, r]) => return .call (← str f) (← vals a) (← vals r)
  | (``Stmt.callIf, #[c, f, a]) => return .callIf (← val c) (← str f) (← vals a)
  | (``Stmt.dispatch, #[x, fs, a, r]) =>
      return .dispatch (← val x) (← list str fs) (← vals a) (← vals r)
  | (``Stmt.ret, #[vs]) => return .ret (← vals vs)
  | _ => bad "a statement" e

def fn (e : Expr) : R Fn := do
  match ← app e with
  | (``Fn.mk, #[n, ps, b]) => return ⟨← str n, ← vals ps, ← list stmt b⟩
  | _ => bad "a function" e

/-! ## The whole guest against its bytecode

The guest expands to one core function per compiled function, in the compiler's order (after
`__jump_tables`), with the compiled function's name; and its `KECCAK` atoms are the compiled
function's `KECCAK` instructions, one for one and in order: the same layouts, as many written
cells as the instruction's `outCells`, and every value an atom reads or writes at one frame offset
of the instructions (`keccakIns`, `keccakOuts`) throughout the function, each constant among them
`SET` at its offset to its word (checked below with the data, the expansion run once). -/

mutual
/-- The atoms of a statement, every branch and arm. -/
def atomsOf : Core.Stmt → List Core.Atom
  | .atom a => [a]
  | .ite _ z n => atomsList z ++ atomsList n
  | .match_ _ arms => atomsArms arms
  | _ => []
def atomsList : List Core.Stmt → List Core.Atom
  | [] => []
  | s :: ss => atomsOf s ++ atomsList ss
def atomsArms : List (List Core.Stmt) → List Core.Atom
  | [] => []
  | a :: as => atomsList a ++ atomsArms as
end

/-- The `KECCAK` atoms of a core function: their read and written values and layouts. -/
def keccakAtoms (f : Core.Fn) : List (List Core.V × List Core.V × Bool × Bool) :=
  (atomsList f.body).filterMap fun
    | .keccak ins outs i o => some (ins, outs, i, o)
    | _ => none

/-- The `KECCAK` instructions of a compiled function: their read and written offsets and
layouts. -/
def keccakInstrs (c : CompiledFunction) : List (List Nat × List Nat × Bool × Bool) :=
  c.chunks.flatten.filterMap fun
    | .keccak m0 m1 m2 m3 tail b8 cap out i o oC =>
        some (keccakIns m0 m1 m2 m3 tail b8 cap, keccakOuts out oC.cellCount, i, o)
    | _ => none

/-- Whether a core function's `KECCAK` atoms are a compiled function's `KECCAK` instructions. -/
def keccakAgree (f : Core.Fn) (c : CompiledFunction) : Bool := Id.run do
  let as := keccakAtoms f
  let is := keccakInstrs c
  if as.length != is.length then return false
  let mut off : Std.HashMap Core.V Nat := {}
  for ((ins, outs, i, o), (ci, co, i', o')) in as.zip is do
    if i != i' || o != o' || ins.length != 13 || outs.length != co.length then return false
    for (v, k) in (ins ++ outs).zip (ci ++ co) do
      match off[v]? with
      | some k' => if k != k' then return false
      | none => off := off.insert v k
  let code := c.chunks.flatten
  return (atomsList f.body).all fun
    | .const v x => match off[v]? with
      | some k => code.any fun
          | .set k' c0 c1 => k' == k && limbsOf x == (c0, c1)
          | _ => false
      | none => true
    | _ => true

/-! ## The data against the expansion -/

set_option compiler.extract_closed false in
/-- The data against the expansion, in an environment holding `coreProgram`. -/
def check (env : Environment) : Except String Unit := do
  let some (.defnInfo d) := env.find? `LeanVM.Guest.coreProgram | throw "no coreProgram"
  let some (.defnInfo c) := env.find? `LeanVM.Guest.Data.coreCount | throw "no coreCount"
  let P ← (list fn d.value).run env
  let n ← (nat c.value).run env
  let Q ← Expand.expandProgram Data.guest
  unless P.length == n && P == Q.map Fn.renumber do
    throw "coreProgram is not the renumbered expansion"
  unless Q.head?.map (·.name) == some "main" && Q.getLast?.map (·.name) == some "walk_path__L12_L8" &&
      Q.map (·.name) == Data.functions.tail.map (·.name) &&
      (Q.zip Data.functions.tail).all fun (f, c) => keccakAgree f c do
    throw "the expansion is not the compiled functions"

end LeanVMTests.Guest.CoreData
