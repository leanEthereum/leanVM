import LeanVM.Guest.CoreData
import LeanVM.Guest.Data.Source
import LeanVM.Guest.Expand

/-!
# The core IR's data

`coreProgram`'s definitions (`Guest/Data/Core*`, noncomputable) read back from their elaborated
terms, and compared with `(Expand.expandProgram Data.guest).map (·.map Fn.renumber)`, both
evaluated without the kernel: the data cannot drift from the source.
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

run_meta do
  let some (.defnInfo d) := (← getEnv).find? ``coreProgram | throwError "no coreProgram"
  let P ← match (list fn d.value).run (← getEnv) with
    | .ok P => pure P
    | .error e => throwError e
  match Expand.expandProgram Data.guest with
  | .ok Q => unless P.length == 1055 && P == Q.map Fn.renumber do
      throwError "coreProgram is not the renumbered expansion"
  | .error e => throwError e

/-! ## Access

By index, by name and against the compiled functions, at the first, a middle and the last
function, at the two largest (`__loop2`, the raw leanXMSS loop with `verify_lean_xmss` inlined, and
`sp_wots`) and at `verify_sig_lean_sphincs`, the first function past `sp_wots` (core 20, compiled
function 21). -/

set_option maxRecDepth 100000

example : coreProgram.length = 1055 := coreProgram_length

example : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

example : coreProgram.find? "__loop2" = some Data.core36 :=
  Program.find?_of_indexOf? (j := 36) (by decide +kernel) rfl

example : coreProgram.find? "sp_wots" = some Data.core19 :=
  Program.find?_of_indexOf? (j := 19) (by decide +kernel) rfl

example : coreProgram.find? "verify_sig_lean_sphincs" = some Data.core20 :=
  Program.find?_of_indexOf? (j := 20) (by decide +kernel) rfl

example : coreProgram.find? "squeeze_point__L18" = some Data.core527 :=
  Program.find?_of_indexOf? (j := 527) (by decide +kernel) rfl

example : coreProgram.find? "walk_path__L18_L4" = some Data.core1054 :=
  Program.find?_of_indexOf? (j := 1054) (by decide +kernel) rfl

example : Data.core19.name = Data.f20.name := name_eq_compiled (j := 19) rfl rfl

example : Data.core20.name = Data.f21.name := name_eq_compiled (j := 20) rfl rfl

example : Data.core36.name = Data.f37.name := name_eq_compiled (j := 36) rfl rfl

example : Data.core990.name = Data.f991.name := name_eq_compiled (j := 990) rfl rfl

end LeanVMTests.Guest.CoreData
