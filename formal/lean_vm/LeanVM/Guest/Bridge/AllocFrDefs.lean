/-
  LeanVM.Guest.Bridge.AllocFrDefs

  The callee frames' sizes checked against the core IR: each frame hint reserves what its call
  site's callee needs.
-/

module

public import LeanVM.Guest.Bridge.AllocDefs
public import LeanVM.Guest.Bridge.PairDefs
public import LeanVM.Guest.B2C.Defs
public import LeanVM.Guest.Memory.Static

/-!
# The frame hints' sizes

`frChk X n cs skip ps body d`: every call statement of the body (`callsAll`, nested ones too) at the site a
frame hint's pointer names fits that hint (`frFits`), but the hints at the offsets `skip`, the callees' frame sizes and loop flags read
off the listed compiled functions `cs` (`calTbl`, by name):

* `alloc _ n` at a `call f`: `f` no loop helper, of frame size `n`;
* `allocArm _ sel sizes` at a `dispatch x fs`: `sel` the cell of `x`, a parameter (`ps`) at a certificate cell or a value a spine atom names, and
  arm `j`'s size `sizes[j]` the frame size of `fs[j]`, no loop helper;
* `allocFrames _ size stop si tail` at a `callIf b f (a0 :: a1 :: _)`: `f` a loop helper ending at its
  second parameter (`loopTail`), of frame size `size = tail`, `stop` the cell of `a1`; the spine sets
  `a0` to `g^e`, `si` its inverse (`e ≤ 1`), and `b` to `c + a1` with `c` set to `g^e` too, or to the
  sum of two distinct constants.
-/

namespace LeanVM.Guest.Bridge

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Check (getF)

@[expose] public section

/-- Every call statement of a statement passes `p`, by the recursor (which the kernel reduces faster
than structural recursion). -/
noncomputable def callsS (p : Stmt → Bool) (s : Stmt) : Bool :=
  Stmt.rec (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun f args rets => p (.call f args rets))
    (fun c f args => p (.callIf c f args)) (fun x fs args rets => p (.dispatch x fs args rets)) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) s

/-- Every call statement of a block passes `p`. -/
noncomputable def callsAll (p : Stmt → Bool) (ss : List Stmt) : Bool :=
  Stmt.rec_1 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun f args rets => p (.call f args rets))
    (fun c f args => p (.callIf c f args)) (fun x fs args rets => p (.dispatch x fs args rets)) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) ss

/-- Every call statement of a list of arms passes `p`. -/
noncomputable def callsArms (p : Stmt → Bool) (as : List (List Stmt)) : Bool :=
  Stmt.rec_2 (motive_1 := fun _ => Bool) (motive_2 := fun _ => Bool) (motive_3 := fun _ => Bool)
    (fun _ => true) (fun _ _ _ bz bn => bz && bn) (fun _ _ ba => ba) (fun f args rets => p (.call f args rets))
    (fun c f args => p (.callIf c f args)) (fun x fs args rets => p (.dispatch x fs args rets)) (fun _ => true)
    true (fun _ _ b bs => b && bs) true (fun _ _ b bs => b && bs) as

/-- A call statement's arguments. -/
def stArgs : Stmt → List V
  | .call _ args _ | .callIf _ _ args | .dispatch _ _ args _ => args
  | _ => []

/-- A call statement's returns. -/
def stRets : Stmt → List V
  | .call _ _ rets | .dispatch _ _ _ rets => rets
  | _ => []

/-- The listed callees' names, frame sizes, loop flags, and whether each ends at its second
parameter. -/
noncomputable def calTbl (cs : List ℕ) : List (String × ℕ × Bool × Bool) :=
  cs.map fun c ↦ ((coreOf c).name, B2C.fsN c, (coreOf c).loop, (coreOf c).loop && (loopTail (coreOf c) none).isSome)

/-- The facts of the callee named `f`. -/
def calFind (tbl : List (String × ℕ × Bool × Bool)) (f : String) : Option (ℕ × Bool × Bool) :=
  (tbl.find? fun x ↦ x.1 == f).map (·.2)

/-- `v` set to `g^e` by an atom of `sp`. -/
def spConst (sp : List Atom) (v : V) (e : ℕ) : Bool :=
  sp.any fun
    | .const x w => x == v && constOk w e
    | _ => false

/-- The constant an atom of `sp` sets `v` to. -/
def spWord (sp : List Atom) (v : V) : Option E :=
  sp.findSome? fun
    | .const x w => if x == v then some w else none
    | _ => none

/-- `g⁻¹`. -/
def gInv : K := K.ofBits 0x800000000000000d

/-- The inverse of `g^e`, `e ≤ 1`. -/
def startInv : ℕ → Option K
  | 0 => some 1
  | 1 => some gInv
  | _ => none

/-- A loop entry's guard `b`: `c + a1` with `c` set to `g^e`, or the sum of two distinct constants. -/
def guardOk (sp : List Atom) (b a1 : V) (e : ℕ) : Bool :=
  sp.any fun
    | .add d x y => d == b && ((spConst sp x e && y == a1) || (spConst sp y e && x == a1) ||
        match spWord sp x, spWord sp y with
        | some w1, some w2 => w1 != w2
        | _, _ => false)
    | _ => false

/-- Arm `j` and those after it: each callee no loop helper, of the size its arm lists. -/
def armsFit (tbl : List (String × ℕ × Bool × Bool)) (sizes : List ℕ) : List String → ℕ → Bool
  | [], _ => true
  | f :: fs, j => (match calFind tbl f with
      | some (m, lp, _) => sizes[j]? == some m && !lp
      | none => false) && armsFit tbl sizes fs (j + 1)

/-- **A frame hint fits a call statement at its site.** -/
noncomputable def frFits (X : AlignCtx) (n : ℕ) (ps : List V) (sp : List Atom) (tbl : List (String × ℕ × Bool × Bool)) :
    Prover.Exec.Hint → Stmt → Bool
  | .alloc _ m, .call f _ _ => match calFind tbl f with
    | some (k, lp, _) => k == m && !lp
    | none => false
  | .allocArm _ sel sizes, .dispatch x fs _ _ =>
      X.locAt x.idx == sel && allocCellOk X n x &&
        ((ps.contains x && (X.extra.lookup x.idx).isNone) || sp.any (fun a ↦ (atomUses a).contains x)) &&
        Nat.blt sizes.length (2 ^ 28) && armsFit tbl sizes fs 0
  | .allocFrames _ size stop si tail, .callIf b f (a0 :: a1 :: _) => match calFind tbl f with
    | some (k, lp, ep) => lp && ep && k == size && tail == size && X.locAt a1.idx == stop && allocCellOk X n a1 &&
        ((spConst sp a0 0 && si == 1 && guardOk sp b a1 0) || (spConst sp a0 1 && si == gInv && guardOk sp b a1 1))
    | none => false
  | _, _ => false

/-- **The frame hints' sizes check** of a function: its context, frame size, listed callees, the
offsets of the frame hints it skips, body and advice. -/
noncomputable def frChk (X : AlignCtx) (n : ℕ) (cs skip : List ℕ) (ps : List V) (body : List Stmt)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  (frames X d).isEmpty || (cs.all (fun c ↦ Nat.ble 1 c && Nat.blt c nFns) &&
    callsAll (fun st ↦ (frames X d).all fun q ↦ skip.contains q.1 || match allocPtr q.2 with
      | some p => (X.siteAt p (stArgs st) (stRets st)).isNone || frFits X n ps (spine body) (calTbl cs) q.2 st
      | none => true) body)

end

end LeanVM.Guest.Bridge
