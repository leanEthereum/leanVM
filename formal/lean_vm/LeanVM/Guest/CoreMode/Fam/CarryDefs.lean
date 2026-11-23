/-
  LeanVM.Guest.CoreMode.Fam.CarryDefs

  The checks behind facts carried down the honest tree at listed parameters: a value in `K`, or
  the exponent tables' base, passed by every call site of the listed callees; the heap witness
  pointers their spines do not pin, in `K` by the carried values.
-/

module

public import LeanVM.Guest.CoreMode.Fam.Down
public import LeanVM.Guest.Bridge.WitDefs
public import LeanVM.Guest.Memory.Family
public import LeanVM.Guest.Memory.ScopeDefs
public import LeanVM.Guest.CoreMode.Gen.CarryNzList
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.Renumber
public meta import LeanVM.Guest.CoreRef

/-!
# Facts carried at listed parameters

`carried`: callee, parameter position, fact (`Kd`: in `K`, or the base of the exponent tables).
A caller passes a fact on when its argument is pinned in its own body (`pin`): in `K`
(`kOf`) when one of the caller's carried values or its loop counter, allocated, loaded or touched
through, range checked, or a product of such on the spine; the tables' base when one of the
caller's carried values or the return of a top-level call of `exponent_tables` (`scanCall`).

`carryG fn`: every call site of `fn` passes each listed callee's carried facts (`siteC`), and each
heap witness pointer of `fn` its spine does not pin (`Bridge.ptrOk`) is in `K` by `kOf`, written
from offset `0`.

Nonzero values of `K` (powers of `g`, `g` generating `K^×`) are carried the same way, at the
parameters `carriedNz` lists, checked in each statement's context (`Memory.allB`): `nzOf` pins a
value nonzero in `K` when it is listed (a carried parameter or the loop counter, `kvNz`), a nonzero
constant of `K`, an address a load, touch or range check reads, a word of a call its callee pins
(`nzUp`: a parameter or return its own body pins), a product of such, a factor of such by one in
`K` (`kIn`), a copy, or a read of a table its context fills with such values at an index range checked against a
constant (`tabNz`); and the values of its own `ownNz` lists, which its body pins on every returning path: copies of
nonzero constants in every arm of a `match` (`armNzB`), table reads at a `match`'s selector (`selTabB`). `carryNzG fn`: every call site of `fn` passes its callees' listed values
(`siteNz`), every dynamic allocation's size is pinned (`nzStmt`), and every listed word of `fn` is
pinned in its own body (`upChk`).
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (spine allocOf loadPtr ptrOk blockAll)

@[expose] public section

/-- A carried fact: in `K`, or the exponent tables' base. -/
inductive Kd where
  | inK
  | tab
  deriving DecidableEq

/-- **The carried parameters**: callee, parameter position, fact. -/
def carried : List (String × ℕ × Kd) :=
  [(name% «main_loop0», 2, .inK), (name% «main_loop0», 3, .inK),
    (name% «main_loop1», 2, .inK), (name% «main_loop1», 3, .inK),
    (name% «main_loop4», 9, .inK), (name% «main_loop4», 14, .tab), (name% «verify_sub», 4, .tab),
    (name% «log2_ceil_in_the_exponent__L0_L34», 1, .tab),
    (name% «log2_ceil_in_the_exponent__L16_L34», 1, .tab), (name% «certify_placement», 1, .tab),
    (name% «verify_tables», 12, .tab)]

/-- A function's carried values of a fact, and its loop counter for `K`. -/
def cvars (fn : Fn) (kd : Kd) : List V :=
  (carried.filterMap fun c => if c.1 == fn.name && c.2.2 == kd then fn.params[c.2.1]? else none) ++
    (if kd == .inK && fn.loop then fn.params.take 1 else [])

/-- An atom puts `v` in `K`: an allocation, a load or touch through it, a range check of it, a
frame address. -/
def pinK (v : V) : Atom → Bool
  | .hint (.alloc d _) => decide (d = v)
  | .hint (.allocDyn d _) => decide (d = v)
  | .load _ p _ => decide (p = v)
  | .touch _ p => decide (p = v)
  | .rangeCheck x y _ _ _ => decide (x = v) || decide (y = v)
  | .frameAddr p _ => decide (p = v)
  | _ => false

/-- **`v` in `K`**: a listed value, pinned by an atom of `sp`, or a product of such, `n` deep. -/
def kOf (kv : List V) (sp : List Atom) : ℕ → V → Bool
  | 0, v => kv.contains v || sp.any (pinK v)
  | n + 1, v => kv.contains v || sp.any (pinK v) || sp.any fun
      | .mul d a b => decide (d = v) && kOf kv sp n a && kOf kv sp n b
      | _ => false

/-- **A top-level call satisfying `p`**, every statement before it free of `ret`. -/
def scanCall (p : String → List V → List V → Bool) : List Stmt → Bool
  | [] => false
  | s :: ss => (match s with | .call f args rets => p f args rets | _ => false) ||
      (Memory.Stmt.noRet s && scanCall p ss)

/-- The depth `kOf` searches. -/
abbrev kDepth : ℕ := 8

/-- **A value of `fn` pinned for a fact.** -/
noncomputable def pin (fn : Fn) : Kd → V → Bool
  | .inK, v => kOf (cvars fn .inK) (spine fn.body) kDepth v
  | .tab, v => (cvars fn .tab).contains v ||
      scanCall (fun f args rets => f == "exponent_tables" && args.isEmpty && rets == [v]) fn.body

/-- **A call site of `fn` passes the carried facts.** -/
noncomputable def siteC (fn : Fn) (f : String) (args _rets : List V) : Bool :=
  carried.all fun c => c.1 != f || match args[c.2.1]? with
    | some a => pin fn c.2.2 a
    | none => false

/-- A heap witness pointer: pinned by the spine, or in `K` by `kOf` and written from offset `0`. -/
noncomputable def witAtomC (fn : Fn) (sp : List Atom) : Atom → Bool
  | .hint (.witness _ (.heap p off len)) =>
      ptrOk sp p || (kOf (cvars fn .inK) sp kDepth p && off == 0 && Nat.blt 0 len)
  | _ => true

/-- **The carried facts' check of one function.** -/
noncomputable def carryG (fn : Fn) : Bool :=
  sitesB (siteC fn) fn.body && blockAll (witAtomC fn (spine fn.body)) fn.body

/-! ## Nonzero values -/

/-- Values equal, their numbers compared first. -/
def veq (a b : V) : Bool := a.idx == b.idx && decide (a = b)

/-- An event puts `v` in `K`: an address it reads, a frame address, an `assertInK`, a constant of
`K`, `v = v·v` (`v` is `0` or `1`). -/
def pinIn (v : V) : Ev → Bool
  | .atom (.mul d a b) => veq d v && veq a v && veq b v
  | .atom (.load _ p _) => veq p v
  | .atom (.touch _ p) => veq p v
  | .atom (.rangeCheck x y _ _ _) => veq x v || veq y v
  | .atom (.frameAddr p _) => veq p v
  | .atom (.assertInK a b) => veq a v || veq b v
  | .atom (.const d w) => veq d v && decide (w.limb 1 = 0)
  | _ => false

/-- `v` a listed value or put in `K` by an event of `sp`. -/
def kIn0 (kv : List V) (sp : List Ev) (v : V) : Bool := kv.any (veq · v) || sp.any (pinIn v)

/-- `v` at `kIn0`, or a product or sum of two such. -/
def kIn1 (kv : List V) (sp : List Ev) (v : V) : Bool :=
  kIn0 kv sp v || sp.any fun
    | .atom (.mul d a b) => veq d v && kIn0 kv sp a && kIn0 kv sp b
    | .atom (.add d a b) => veq d v && kIn0 kv sp a && kIn0 kv sp b
    | _ => false

/-- **`v` in `K`**: a listed value, put in `K` by an event of `sp`, a product of such, `n` deep, or a sum of
values at `kIn1`. -/
def kIn (kv : List V) (sp : List Ev) : ℕ → V → Bool
  | 0, v => kv.any (veq · v) || sp.any (pinIn v)
  | n + 1, v => kv.any (veq · v) || sp.any (pinIn v) || sp.any fun
      | .atom (.mul d a b) => veq d v && kIn kv sp n a && kIn kv sp n b
      | .atom (.add d a b) => veq d v && kIn1 kv sp a && kIn1 kv sp b
      | _ => false

/-- A call's word `v` pinned by its callee: the position of `v` among the call's words listed for
the callee (`nzUp`). -/
def upAt (g : String) (ws : List V) (v : V) : Bool :=
  nzUp.any fun c => (match ws[c.2]? with
    | some w => veq w v
    | none => false) && c.1 == g

/-- An event puts `v` nonzero in `K`: a nonzero constant of `K`, an address a load, touch or range
check reads, a word of a call its callee pins. -/
def pinNz (v : V) : Ev → Bool
  | .atom (.const d w) => veq d v && decide (w.limb 1 = 0) && !decide (w.limb 0 = 0)
  | .atom (.load _ p _) => veq p v
  | .atom (.touch _ p) => veq p v
  | .atom (.rangeCheck x y _ _ _) => veq x v || veq y v
  | .call g args rets => upAt g (args ++ rets) v
  | _ => false

/-- The exponent of a word of `K` the guest's powers name. -/
noncomputable def powOf (w : LeanVM.Parameters.E) : Option ℕ :=
  if w.limb 1 = 0 then Data.powTree.find (w.limb 0).toBitVec.toNat else none

/-- **A table read at `T·J·g^off`** (`tabAt`): `J` range checked against the constant `g^m`, `m < 2^28`, and the
context storing at each `T·g^(t + off)`, `t ≤ m`, a value `nz` pins. -/
noncomputable def tabAt (sp : List Ev) (nz : V → Bool) (T J : V) (off : ℕ) : Bool :=
  sp.any fun
    | .atom (.rangeCheck x _ _ _ k) => veq x J && sp.any fun
        | .atom (.const d c) => veq d k && match powOf c with
            | some m => decide (m < 2 ^ 28) && (List.range (m + 1)).all fun t => sp.any fun
                | .atom (.load w T' o) => veq T' T && o == t + off && nz w
                | _ => false
            | none => false
        | _ => false
    | _ => false

/-- **A read at `p·g^off` of a table** (`tabNz`): `p = T·J`, either order, at `tabAt`. -/
noncomputable def tabNz (sp : List Ev) (nz : V → Bool) (p : V) (off : ℕ) : Bool :=
  sp.any fun
    | .atom (.mul q a b) => veq q p && (tabAt sp nz a b off || tabAt sp nz b a off)
    | _ => false

/-- **`v` nonzero in `K`**: a listed value, pinned by an event of `sp`, a product of such, a factor
of such by a value in `K`, a copy (an `assertEq` too), or a table read (`tabNz`), `n` deep. -/
noncomputable def nzOf (kv : List V) (sp : List Ev) : ℕ → V → Bool
  | 0, v => kv.any (veq · v) || sp.any (pinNz v)
  | n + 1, v => kv.any (veq · v) || sp.any (pinNz v) || sp.any fun
      | .atom (.mul d a b) => (veq d v && nzOf kv sp n a && nzOf kv sp n b) ||
          (veq b v && kIn kv sp kDepth a && nzOf kv sp n d) ||
          (veq a v && kIn kv sp kDepth b && nzOf kv sp n d)
      | .atom (.copy d s) => (veq d v && nzOf kv sp n s) || (veq s v && nzOf kv sp n d)
      | .atom (.assertEq d s) => (veq d v && nzOf kv sp n s) || (veq s v && nzOf kv sp n d)
      | .atom (.load d p off) => veq d v && tabNz sp (nzOf kv sp n) p off
      | _ => false

/-- The depth `nzOf` searches. -/
abbrev nzDepth : ℕ := 12

/-- **`v` pinned nonzero in every arm of a top-level `match`** (`armNzB`), before any statement that may return,
on the arm's own spine (`nzOf`, nothing listed). -/
noncomputable def armNzB (v : V) : List Stmt → Bool
  | [] => false
  | s :: ss => (match s with
      | .match_ _ (a :: as) => (a :: as).all fun b => nzOf [] (spineE b) nzDepth v
      | _ => false) || (Bridge.noRet [s] && armNzB v ss)

/-- The selectors of the top-level `match`es before any statement that may return, with their numbers of arms. -/
noncomputable def topSelsC : List Stmt → List (V × ℕ)
  | [] => []
  | s :: ss => (match s with
      | .match_ x arms => [(x, arms.length)]
      | _ => []) ++ (bif Bridge.noRet [s] then topSelsC ss else [])

/-- **A table read at `T·J·g^off`, `J` a selector** (`selTabAt`): of `m` arms (`sels`), the spine storing at each
`T·g^(t + off)`, `t < m`, a value it pins nonzero. -/
noncomputable def selTabAt (sp : List Ev) (sels : List (V × ℕ)) (T J : V) (off : ℕ) : Bool :=
  sels.any fun c => veq c.1 J && (List.range c.2).all fun t => sp.any fun
    | .atom (.load w T' o) => veq T' T && o == t + off && nzOf [] sp nzDepth w
    | _ => false

/-- **`v` read by a body's spine from a table at a selector** (`selTabB`): at `p·g^off`, `p = T·J` (either order),
at `selTabAt`. -/
noncomputable def selTabB (body : List Stmt) (v : V) : Bool :=
  (spineE body).any fun
    | .atom (.load d p off) => veq d v && (spineE body).any (fun
        | .atom (.mul q a b) => veq q p && (selTabAt (spineE body) (topSelsC body) a b off ||
            selTabAt (spineE body) (topSelsC body) b a off)
        | _ => false)
    | _ => false

/-- **A listed value of `fn`'s own pinned by its body** (`ownNz`) on every returning path: `armNzB` or `selTabB`. -/
noncomputable def ownChk (fn : Fn) (v : V) : Bool := armNzB v fn.body || selTabB fn.body v

/-- The values of `fn` carried nonzero in `K`: its listed parameters, its loop counter, and its listed own values
(`ownNz`, checked by `ownChk`). -/
def kvNz (fn : Fn) : List V :=
  (carriedNz.filterMap fun c => if c.1 == fn.name then fn.params[c.2]? else none) ++
    (if fn.loop then fn.params.take 1 else []) ++
    ownNz.filterMap fun c => if c.1 == fn.name then some (V.n c.2) else none

/-- **A call site passes its callee's listed values.** -/
noncomputable def siteNz (kv : List V) (sp : List Ev) (f : String) (args : List V) : Bool :=
  carriedNz.all fun c => c.1 != f || match args[c.2]? with
    | some a => nzOf kv sp nzDepth a
    | none => false

/-- **The nonzero facts' check of a statement** in its context: a call site passes its callees'
listed values, a dynamic allocation's size is nonzero in `K`. -/
noncomputable def nzStmt (kv : List V) (sp : List Ev) : Stmt → Bool
  | .atom (.hint (.allocDyn _ s)) => nzOf kv sp nzDepth s
  | .call f args _ => siteNz kv sp f args
  | .callIf _ f args => siteNz kv sp f args
  | .dispatch _ fs args _ => fs.all fun f => siteNz kv sp f args
  | _ => true

/-- A return's value at `j` pinned nonzero in its context. -/
noncomputable def retNz (j : ℕ) (sp : List Ev) : Stmt → Bool
  | .ret vs => match vs[j]? with
    | some v => nzOf [] sp nzDepth v
    | none => false
  | _ => true

/-- **A listed word of `fn` pinned by its own body**: parameter `i` on its spine, or return
`i - np` at every return. -/
noncomputable def upChk (fn : Fn) (i : ℕ) : Bool :=
  match fn.params[i]? with
  | some p => nzOf [] (spineE fn.body) nzDepth p
  | none => allB (fun sp s => retNz (i - fn.params.length) sp s) fn.body (spineE fn.body)

/-- **The nonzero facts' check of one function.** -/
noncomputable def carryNzG (fn : Fn) : Bool :=
  allB (nzStmt (kvNz fn)) fn.body (spineE fn.body) && nzUp.all (fun c => c.1 != fn.name || upChk fn c.2) &&
    ownNz.all fun c => c.1 != fn.name || ownChk fn (V.n c.2)

end

end LeanVM.Guest.Res
