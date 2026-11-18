/-
  LeanVM.Compiler.Consts

  The constant parameters of a program's loop helpers: an argument every call of the helper passes
  as the same constant word, the helper's closing call passing its own parameter through.
-/

module

public import LeanVM.Compiler.Place

/-!
# Constant parameters

A registered loop helper's closing call copies every argument into the next frame of its run. An
argument the closing call passes through unchanged, and that every other call passes as one
constant word, holds that word in every frame of the run, so the copy can be a `SET`.

A table of constant parameters is a function from a function's name to its entries: argument
positions and their words. The back end's is `constsOf (loopTable p)`, what each loop helper's
`TracedFn.consts` holds.

* `ConstsOk T p`: the table is right of the program `p`: it names nothing of `main`, and, by a
  check of each body, at each call of a function, the arguments its entries name are values the
  statements before the call on its path are known to have set to their words, by a `const` atom
  of the block or of an enclosing one (`blockOk`), or the function's own parameters its entries
  name (`entryKnown`). `lowerProgram` checks it of the back end's table.
* `constTable p`: a table for `p`: for each registered loop helper, the arguments the calls
  outside it pass as known constants, each kept only where every call agrees, the helper's own
  calls included; checked by `ConstsOk`, and empty if the check fails. `withConstTable p` writes it
  into the functions (`TracedFn.consts`).

`Sound/Consts.lean` proves that a right table's facts follow from a function's obligations.
-/

namespace LeanVM.Compiler

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- Argument positions and their words, by function: the table `constTable` builds. -/
abbrev Consts := SMap (List (Nat × E))

/-- A function's entries. -/
def Consts.at (T : Consts) (f : String) : List (Nat × E) := T.getD f []

/-- Values and the words they are known to hold. -/
abbrev Known := List (V × E)

/-- What a statement teaches: a `const` atom's value holds its word. -/
def learn (kn : Known) : Stmt → Known
  | .atom (.const d c) => (d, c) :: kn
  | _ => kn

/-- The arguments of a call of `f` that `T` names are known to hold their words. -/
def argsOk (T : String → List (Nat × E)) (kn : Known) (f : String) (args : List V) : Bool :=
  (T f).all fun x => match args[x.1]? with
    | some v => kn.contains (v, x.2)
    | none => false

mutual
/-- Every call in the statement passes the words `T` names, `kn` known before it. -/
def stmtOk (T : String → List (Nat × E)) (kn : Known) : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => blockOk T kn z && blockOk T kn n
  | .match_ _ arms => armsOk T kn arms
  | .call f args _ => argsOk T kn f args
  | .callIf _ f args => argsOk T kn f args
  | .dispatch _ fs args _ => fs.all fun f => argsOk T kn f args
  | .ret _ => true

/-- Every call in the block passes the words `T` names, each statement knowing what the ones
before it taught. -/
def blockOk (T : String → List (Nat × E)) (kn : Known) : List Stmt → Bool
  | [] => true
  | s :: ss => stmtOk T kn s && blockOk T (learn kn s) ss

/-- Every call in the arms passes the words `T` names. -/
def armsOk (T : String → List (Nat × E)) (kn : Known) : List (List Stmt) → Bool
  | [] => true
  | a :: as => blockOk T kn a && armsOk T kn as
end

/-- What a function knows at its entry: its parameters `T` names hold their words. -/
def entryKnown (T : String → List (Nat × E)) (f : Fn) : Known :=
  (T f.name).filterMap fun x => (f.params[x.1]?).map (·, x.2)

/-- **The table is right of the program**: it names nothing of `main`, which no call enters, and
every call in every body passes the words it names. -/
def ConstsOk (T : String → List (Nat × E)) (p : Program) : Bool :=
  (T "main").isEmpty && p.all fun f => blockOk T (entryKnown T f) f.body

/-! ## The table the back end uses -/

/-- The words a call of `f` passes known, by argument position; `none` for a call the table does
not follow (`self` excluded, or not a registered loop helper). -/
def callKnown (loops : Loops) (self : Option String) (kn : Known) (f : String) (args : List V) :
    Option (List (Nat × E)) :=
  if self == some f || !((loops[f]?).any (·.registered)) then none
  else some (args.zipIdx.filterMap fun (v, k) => (kn.lookup v).map (k, ·))

/-- Meet a call's known arguments into the table: the first call sets them, a later one keeps
those both agree on. -/
def meet (acc : Consts) (f : String) : Option (List (Nat × E)) → Consts
  | none => acc
  | some here =>
      match acc[f]? with
      | none => acc.insert f here
      | some prev => acc.insert f (prev.filter here.contains)

mutual
/-- The known arguments of the calls in a statement, met into `acc`. -/
def collectStmt (loops : Loops) (self : Option String) (kn : Known) (acc : Consts) :
    Stmt → Consts
  | .atom _ => acc
  | .ite _ z n => collectBlock loops self kn (collectBlock loops self kn acc z) n
  | .match_ _ arms => collectArms loops self kn acc arms
  | .call f args _ => meet acc f (callKnown loops self kn f args)
  | .callIf _ f args => meet acc f (callKnown loops self kn f args)
  | .dispatch _ fs args _ =>
      fs.foldl (fun acc f => meet acc f (callKnown loops self kn f args)) acc
  | .ret _ => acc

def collectBlock (loops : Loops) (self : Option String) (kn : Known) (acc : Consts) :
    List Stmt → Consts
  | [] => acc
  | s :: ss => collectBlock loops self (learn kn s) (collectStmt loops self kn acc s) ss

def collectArms (loops : Loops) (self : Option String) (kn : Known) (acc : Consts) :
    List (List Stmt) → Consts
  | [] => acc
  | a :: as => collectArms loops self kn (collectBlock loops self kn acc a) as
end

/-- The table restricted to what every call agrees on, each function's own calls included and
its entries known at its entry. -/
def refineConsts (loops : Loops) (p : Program) (T : Consts) : Consts :=
  let seen := p.foldl (fun acc f => collectBlock loops none (entryKnown T.at f) acc f.body) {}
  p.foldl (fun acc f =>
    match T[f.name]? with
    | none => acc
    | some xs => acc.insert f.name (xs.filter (seen.at f.name).contains)) {}

/-- **The constant parameters of the program's registered loop helpers**: the arguments the calls
outside each pass as known words, refined until each function's own calls agree, and checked. -/
def constTable (p : List TracedFn) : Consts :=
  let loops := loopTable p
  let core := p.map (·.core)
  let outside := core.foldl (fun acc f => collectBlock loops (some f.name) [] acc f.body) {}
  let T := (List.range 4).foldl (fun T _ => refineConsts loops core T) outside
  if ConstsOk T.at core then T else {}

/-- **The program with its constant parameters**: each function's `TracedFn.consts` its entries in
`constTable`. -/
def withConstTable (p : List TracedFn) : List TracedFn :=
  let T := constTable p
  p.map fun tf => { tf with consts := T.at tf.core.name }

end
end LeanVM.Compiler
