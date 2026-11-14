/-
  LeanVM.Guest.Backend.Sound.Obl.Check

  A decidable analysis of a core function that finds each selector's range and each callee's
  precondition among the statements before it on its path.
-/

module

public import LeanVM.Guest.Core
public import LeanVM.Guest.Word

/-!
# Selectors and preconditions found in the function

The back end's obligations (`OblList`, `Sound/Spec.lean`) ask, at each `match` and `dispatch`,
that the selector be `g^j` with `j` below the arm count, and at each call that the callee's
precondition hold, each given what the statements before it on its path establish. `chk` walks
a block and looks for those facts in what precedes the site (`Hyp`, most recent first):

* a range check `rangeCheck x _ _ _ k` with `k` set to `g^(K-1)`: `x = g^e`, `e < K`;
* a constant `x = g^j`, or the arm `j` of an enclosing `match` on `x`;
* a selector bounded by booleanity, `1 + b·(1 + g^k)` with `b·b = b`: `g^0` or `g^k`;
* a product of two bounded selectors (`g^e₁ · g^e₂`), a copy of one;
* a word read at `p·g^c` where the precondition bounds the words there (`Sig.mem`);
* an argument the precondition bounds (`Sig.pre`), an argument or return of a call its
  callee's postcondition bounds (`Sig.post`).

The preconditions are a table `Tab`: per function, bounds on its arguments, bounds on words read
through its arguments, and bounds on its returns. A call is accepted when its callee's table
entries hold of its arguments in the same way. `Obl.CheckSound` proves the analysis sound.
-/

namespace LeanVM.Guest.Backend.Obl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- What a function asks of its callers and promises them, as bounds on exponents: argument
`i` is `g^e` with `e < n` (`pre`), the word at argument `i` times `g^c` is `g^e` with `e < n`
(`mem`), and after the call frame cell `2 + i` (an argument for `i` below the arity, else a
return) is `g^e` with `e < n` (`post`); argument `i` is in the relation tagged `t` (`xpre`,
`(i, t)`), and after the call frame cell `2 + i` is (`xpost`, the relations' meaning a parameter
of the soundness theorems, `xpost` taken from outside the analysis); `ext`: the function asks more
than that, and the analysis never accepts a call of it. -/
structure Sig where
  pre : List (Nat × Nat) := []
  mem : List (Nat × Nat × Nat) := []
  post : List (Nat × Nat) := []
  xpre : List (Nat × Nat) := []
  xpost : List (Nat × Nat) := []
  ext : Bool := false
  deriving DecidableEq, Repr

/-- The table of signatures, by function name (a function it does not name has none), and the
powers of `g` the analysis knows beyond `g^j`, `j < 64`, as `(bits, exponent)`. -/
structure Tab where
  sigs : List (String × Sig)
  pows : List (Nat × Nat) := []

/-- A name as the bytes of its encoding, which the kernel compares faster than strings. -/
def nameKey (s : String) : List Nat := s.toByteArray.data.toList.map UInt8.toNat

/-- A function's signature in the table: the first entry whose name has the same bytes. -/
def Tab.sig (T : Tab) (f : String) : Sig :=
  let k := nameKey f
  match T.sigs.find? (fun p => nameKey p.1 == k) with
  | some p => p.2
  | none => {}

/-- What the statements before a site establish, most recent first. -/
inductive Hyp where
  /-- An atom that holds. -/
  | atom (a : Atom)
  /-- The arm `j` of a `match` on `x`: `x = g^j`. -/
  | arm (x : V) (j : Nat)
  /-- A call of `f` on `args` returned `rets`. -/
  | ret (f : String) (args rets : List V)
  /-- The function's own precondition: `x = g^e`, `e < n`. -/
  | pre (x : V) (n : Nat)
  /-- The function's own precondition: the word at `x · g^c` is `g^e`, `e < n`. -/
  | mem (x : V) (c n : Nat)
  /-- `x` is in the relation tagged `t`. -/
  | rel (v : V) (t : Nat)

/-- Two values are one, their index compared first. -/
def veq (a b : V) : Bool := a.idx == b.idx && a.tag == b.tag && a.path == b.path

/-- `j` with `2^j = a`, `j < 64`. -/
def log2Exact (a : Nat) : Option Nat :=
  let j := Nat.log2 a
  if 2 ^ j = a ∧ j < 64 then some j else none

/-- The low limb's bits of a word whose high limb is zero. -/
def lowBits (c : E) : Option Nat :=
  if (c.limb 1).toBitVec.toNat = 0 then some (c.limb 0).toBitVec.toNat else none

/-- `j` with `c = g^j`, read off the bits of `c`: `g` is the polynomial `x`, so `g^j` is the
word `2^j` for `j < 64`; beyond, a power the table lists. -/
def powOf (pows : List (Nat × Nat)) (c : E) : Option Nat :=
  (lowBits c).bind fun a => (log2Exact a).or ((pows.find? (·.1 == a)).map (·.2))

/-- `k` with `c = 1 + g^k`, `1 ≤ k < 64`. -/
def oppOf (c : E) : Option Nat :=
  (lowBits c).bind fun a =>
    match log2Exact (a - 1) with
    | some k => if 1 ≤ k ∧ 2 ^ k + 1 = a then some k else none
    | none => none

/-- The least of two optional bounds. -/
def minO : Option Nat → Option Nat → Option Nat
  | some a, some b => some (min a b)
  | some a, none => some a
  | none, b => b

/-- `p` bounded by `n`. -/
def leO (o : Option Nat) (n : Nat) : Bool :=
  match o with
  | some m => Nat.ble m n
  | none => false

section Look

variable (T : Tab)

/-- `x = g^j`, exactly: a constant or an arm. -/
def gpOf (ctx : List Hyp) (x : V) : Option Nat :=
  ctx.findSome? fun h => match h with
    | .atom (.const d c) => if veq d x then powOf T.pows c else none
    | .arm y j => if veq y x then some j else none
    | _ => none

/-- `x = 1 + g^k`, a constant. -/
def oppAt (ctx : List Hyp) (x : V) : Option Nat :=
  ctx.findSome? fun h => match h with
    | .atom (.const d c) => if veq d x then oppOf c else none
    | _ => none

/-- `x · x = x`. -/
def isBool (ctx : List Hyp) (x : V) : Bool :=
  ctx.any fun h => match h with
    | .atom (.mul d a b) => veq d x && veq a x && veq b x
    | _ => false

/-- `u = b · (1 + g^k)` with `b · b = b`: `k`. -/
def bscOf (ctx : List Hyp) (u : V) : Option Nat :=
  ctx.findSome? fun h => match h with
    | .atom (.mul d a b) =>
        if veq d u then
          (if isBool ctx a then oppAt ctx b else none).or (if isBool ctx b then oppAt ctx a else none)
        else none
    | _ => none

/-- The bound one hypothesis puts on the word at `x · g^c`. -/
def hypMem (x : V) (c : Nat) : Hyp → Option Nat
  | .mem y c' n => if veq y x && c' == c then some n else none
  | _ => none

/-- The word at `x · g^c` bounded by `n`: the precondition's bound on memory. -/
def memOf (ctx : List Hyp) (x : V) (c : Nat) : Option Nat :=
  ctx.foldl (fun o h => minO o (hypMem x c h)) none

/-- The bound a callee's postcondition gives `x`, argument or return of the call: its frame
cells past the first two, `args ++ rets`. -/
def postOf (f : String) (cells : List V) (x : V) : Option Nat :=
  (T.sig f).post.foldl (fun o p => minO o (if veq (cells.getD p.1 default) x && p.1 < cells.length
    then some p.2 else none)) none

/-- The bound one hypothesis puts on `x`, the bounds of other values given by `rec` (products
and copies). -/
def hypB (ctx : List Hyp) (x : V) (rec : Option (V → Option Nat)) : Hyp → Option Nat
  | .atom (.const d c) => if veq d x then (powOf T.pows c).map (· + 1) else none
  | .arm y j => if veq y x then some (j + 1) else none
  | .pre y n => if veq y x then some n else none
  | .ret f args rets => postOf T f (args ++ rets) x
  | .atom (.rangeCheck y _ _ _ k) =>
      if veq y x then
        match gpOf T ctx k with
        | some j => if j < 2 ^ 32 then some (j + 1) else none
        | none => none
      else none
  | .atom (.load d p c) => if veq d x then memOf ctx p c else none
  | .atom (.add d a b) =>
      if veq d x then
        if gpOf T ctx a == some 0 then (bscOf ctx b).map (· + 1)
        else if gpOf T ctx b == some 0 then (bscOf ctx a).map (· + 1) else none
      else none
  | .atom (.copy d s) =>
      match rec with
      | none => none
      | some r => if veq d x then r s else if veq s x then r d else none
  | .atom (.mul d a b) =>
      match rec with
      | none => none
      | some r =>
        if veq d x then
          match r a, r b with
          | some n₁, some n₂ => some (n₁ + n₂ - 1)
          | _, _ => none
        else none
  | _ => none

/-- **The bound on a selector**: the least `n` such that `x = g^e` with `e < n` follows from one
hypothesis, products and copies followed `fuel` deep. -/
def bnd : Nat → List Hyp → V → Option Nat
  | 0, ctx, x => ctx.foldl (fun o h => minO o (hypB T ctx x none h)) none
  | f + 1, ctx, x => ctx.foldl (fun o h => minO o (hypB T ctx x (some (bnd f ctx)) h)) none

/-- The depth of products and copies `bndLe` follows. -/
def fuel0 : Nat := 3

/-- `x` bounded by `n` by some hypothesis: the first that does, products and copies followed
`fuel0 + 1` deep. -/
def bndLe (ctx : List Hyp) (x : V) (n : Nat) : Bool :=
  ctx.any fun h => leO (hypB T ctx x (some (bnd T fuel0 ctx)) h) n

/-- The word at `x · g^c` bounded by `n` by some hypothesis. -/
def memLe (ctx : List Hyp) (x : V) (c n : Nat) : Bool :=
  ctx.any fun h => leO (hypMem x c h) n

/-- `v` in the relation tagged `t` by some hypothesis: the precondition, a fact, or a callee's
`xpost`. -/
def xLe (ctx : List Hyp) (v : V) (t : Nat) : Bool :=
  ctx.any fun h => match h with
    | .rel y t' => veq y v && t' == t
    | .ret f args rets => (T.sig f).xpost.any fun p =>
        p.2 == t && p.1 < (args ++ rets).length && veq ((args ++ rets).getD p.1 default) v
    | _ => false

/-- A call of `f` on `args` meets `f`'s precondition. -/
def callOk (ctx : List Hyp) (f : String) (args : List V) : Bool :=
  let s := T.sig f
  !s.ext && s.pre.all (fun p => p.1 < args.length && bndLe T ctx (args.getD p.1 default) p.2) &&
    s.mem.all (fun m => m.1 < args.length && memLe ctx (args.getD m.1 default) m.2.1 m.2.2) &&
    s.xpre.all (fun p => p.1 < args.length && xLe T ctx (args.getD p.1 default) p.2)

/-- The hypotheses after a statement, for the statements after it in its block. -/
def after (ctx : List Hyp) : Stmt → List Hyp
  | .atom a => .atom a :: ctx
  | .call f args rets => .ret f args rets :: ctx
  | _ => ctx

/-- What a function promises at its returns: its parameters and the bounds of its frame cells
past the first two (`Sig.post`). -/
structure Want where
  pars : List V
  post : List (Nat × Nat)

mutual
/-- **The analysis of a statement**: each selector bounded by its arm count, each call meeting
its callee's precondition, and at each `return` the frame cells bounded as `post` says. -/
def chkS (post : Want) (ctx : List Hyp) : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => chkL post ctx z && chkL post ctx n
  | .match_ x arms => bndLe T ctx x arms.length && chkA post ctx x 0 arms
  | .call f args _ => callOk T ctx f args
  | .callIf _ f args => callOk T ctx f args
  | .dispatch x fs args _ => bndLe T ctx x fs.length && fs.all (callOk T ctx · args)
  | .ret vs => post.post.all fun p =>
      p.1 < (post.pars ++ vs).length && bndLe T ctx ((post.pars ++ vs).getD p.1 default) p.2

/-- The analysis of a block. -/
def chkL (post : Want) (ctx : List Hyp) : List Stmt → Bool
  | [] => true
  | s :: ss => chkS post ctx s && chkL post (after ctx s) ss

/-- The analysis of the arms of a `match` on `x`, arm `j` first. -/
def chkA (post : Want) (ctx : List Hyp) (x : V) : Nat → List (List Stmt) → Bool
  | _, [] => true
  | j, a :: as => chkL post (.arm x j :: ctx) a && chkA post ctx x (j + 1) as
end

/-- The hypotheses a function starts with: its precondition on its parameters. -/
def entry (params : List V) (s : Sig) : List Hyp :=
  s.pre.filterMap (fun p => (params[p.1]?).map (Hyp.pre · p.2)) ++
    s.mem.filterMap (fun m => (params[m.1]?).map (Hyp.mem · m.2.1 m.2.2)) ++
    s.xpre.filterMap (fun p => (params[p.1]?).map (Hyp.rel · p.2))

/-- **The analysis of a function**: its body, from its precondition, with its postcondition at
each `return`. -/
def chkFn (f : Fn) : Bool :=
  chkL T ⟨f.params, (T.sig f.name).post⟩ (entry f.params (T.sig f.name)) f.body

/-- The facts given at statement `i` of a block. -/
def factsAt (facts : List (Nat × Hyp)) (i : Nat) : List Hyp :=
  facts.filterMap fun p => if p.1 == i then some p.2 else none

/-- **The analysis of a block with facts from outside**: each fact `(i, h)` joins the hypotheses
at statement `i`. -/
def chkT (post : Want) (facts : List (Nat × Hyp)) : Nat → List Hyp → List Stmt → Bool
  | _, _, [] => true
  | i, ctx, s :: ss =>
      chkS T post (factsAt facts i ++ ctx) s &&
        chkT post facts (i + 1) (after (factsAt facts i ++ ctx) s) ss

/-- The analysis of a function, facts from outside given at statements of its body. -/
def chkFnF (facts : List (Nat × Hyp)) (f : Fn) : Bool :=
  chkT T ⟨f.params, (T.sig f.name).post⟩ facts 0 (entry f.params (T.sig f.name)) f.body

end Look

end
end LeanVM.Guest.Backend.Obl
