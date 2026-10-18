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
  | (``word, #[a, b, c]) => return word (← nat a) (← nat b) (← nat c)
  | _ => bad "a word" e

def vals (e : Expr) : R (List V) := list val e

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
  | (``Atom.blake2s, #[m0, m1, m2, m3, c0, c1, o0, o1, md]) =>
      return .blake2s (← val m0) (← val m1) (← val m2) (← val m3) (← val c0) (← val c1)
        (← val o0) (← val o1) (← val md)
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
  | .ok Q => unless P.length == 1043 && P == Q.map Fn.renumber do
      throwError "coreProgram is not the renumbered expansion"
  | .error e => throwError e

/-! ## Access

By index, by name and against the compiled functions, at the first, a middle and the last
function and at the two largest. -/

set_option maxRecDepth 100000

example : coreProgram.length = 1043 := coreProgram_length

example : coreProgram.find? "main" = some Data.core0 :=
  Program.find?_of_indexOf? (j := 0) (by decide +kernel) rfl

example : coreProgram.find? "verify_lean_xmss" = some Data.core16 :=
  Program.find?_of_indexOf? (j := 16) (by decide +kernel) rfl

example : coreProgram.find? "verify_sig_lean_sphincs" = some Data.core17 :=
  Program.find?_of_indexOf? (j := 17) (by decide +kernel) rfl

example : coreProgram.find? "child_claims_tail__L24" = some Data.core521 :=
  Program.find?_of_indexOf? (j := 521) (by decide +kernel) rfl

example : coreProgram.find? "__loop487" = some Data.core1042 :=
  Program.find?_of_indexOf? (j := 1042) (by decide +kernel) rfl

example : Data.core17.name = Data.f18.name := name_eq_compiled (j := 17) rfl rfl

example : Data.core1042.name = Data.f1043.name := name_eq_compiled (j := 1042) rfl rfl

end LeanVMTests.Guest.CoreData
