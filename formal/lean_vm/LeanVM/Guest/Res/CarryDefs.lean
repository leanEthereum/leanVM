/-
  LeanVM.Guest.Res.CarryDefs

  The checks behind facts carried down the honest tree at listed parameters: a value in `K`, or
  the exponent tables' base, passed by every call site of the listed callees; the heap witness
  pointers their spines do not pin, in `K` by the carried values.
-/

module

public import LeanVM.Guest.Res.Down
public import LeanVM.Guest.Bridge.WitDefs
public import LeanVM.Guest.Memory.Family
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
    (name% «log2_ceil_in_the_exponent__L16_L34», 1, .tab)]

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

end

end LeanVM.Guest.Res
