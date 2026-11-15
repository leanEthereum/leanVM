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
public import LeanVM.Guest.Res.LoopDefs

/-!
# The frame hints' sizes

`frChk X n cs skip ps body d`: every call statement of the body (`callsSpL`, nested ones too) at the site a
frame hint's pointer names fits that hint (`frFits`), but the hints at the offsets `skip`, the callees' frame sizes, loop flags
and ends read off the listed compiled functions `cs` (`calTbl`, by name). The atoms `sp` and the values `nm` a statement reads
facts from are those on every path through it: each enclosing block's spine (`spine`), and the returns of its spine's calls
(`spineNamed`).

* `alloc _ n` at a `call f`: `f` no loop helper, of frame size `n`; or a loop helper from `g^e` (`e ≤ 1`) to a constant end
  `g^K`, its `K - e + 1` frames;
* `allocArm _ sel sizes` at a `dispatch x fs`: `sel` the cell of `x`, a parameter (`ps`) at a certificate cell, a value a
  spine atom names or a spine call returns, and arm `j`'s size `sizes[j]` the frame size of `fs[j]`, no loop helper;
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

/-- The listed callees' names, frame sizes, loop flags and loop ends (`Res.endOfFn`). -/
noncomputable def calTbl (cs : List ℕ) : List (String × ℕ × Bool × Option (Option ℕ)) :=
  cs.map fun c ↦ ((coreOf c).name, B2C.fsN c, (coreOf c).loop, Res.endOfFn (coreOf c))

/-- The facts of the callee named `f`. -/
def calFind (tbl : List (String × ℕ × Bool × Option (Option ℕ))) (f : String) : Option (ℕ × Bool × Option (Option ℕ)) :=
  (tbl.find? fun x ↦ x.1 == f).map (·.2)

/-- The values the calls on a block's spine return. -/
noncomputable def spineNamed : List Stmt → List V
  | .atom _ :: ss => spineNamed ss
  | .call _ _ rets :: ss => rets ++ spineNamed ss
  | .callIf .. :: ss => spineNamed ss
  | .dispatch .. :: ss => spineNamed ss
  | .ite _ z n :: ss => bif noRet z && noRet n then spineNamed ss else []
  | .match_ _ arms :: ss => bif noRetArms arms then spineNamed ss else []
  | _ => []

/-- Every call statement of a statement passes `p` with the atoms and values on every path through it,
each block adding its spine's, by the recursor. -/
noncomputable def callsSpS (p : List Atom → List V → Stmt → Bool) (s : Stmt) : List Atom → List V → Bool :=
  Stmt.rec (motive_1 := fun _ => List Atom → List V → Bool) (motive_2 := fun _ => List Atom → List V → Bool)
    (motive_3 := fun _ => List Atom → List V → Bool)
    (fun _ _ _ => true)
    (fun _ z n bz bn sp nm => bz (sp ++ spine z) (nm ++ spineNamed z) && bn (sp ++ spine n) (nm ++ spineNamed n))
    (fun _ _ ba sp nm => ba sp nm)
    (fun f args rets sp nm => p sp nm (.call f args rets))
    (fun c f args sp nm => p sp nm (.callIf c f args))
    (fun x fs args rets sp nm => p sp nm (.dispatch x fs args rets))
    (fun _ _ _ => true)
    (fun _ _ => true)
    (fun _ _ b bs sp nm => b sp nm && bs sp nm)
    (fun _ _ => true)
    (fun a _ ba bas sp nm => ba (sp ++ spine a) (nm ++ spineNamed a) && bas sp nm) s

/-- `callsSpS` of a block. -/
noncomputable def callsSpL (p : List Atom → List V → Stmt → Bool) (ss : List Stmt) : List Atom → List V → Bool :=
  Stmt.rec_1 (motive_1 := fun _ => List Atom → List V → Bool) (motive_2 := fun _ => List Atom → List V → Bool)
    (motive_3 := fun _ => List Atom → List V → Bool)
    (fun _ _ _ => true)
    (fun _ z n bz bn sp nm => bz (sp ++ spine z) (nm ++ spineNamed z) && bn (sp ++ spine n) (nm ++ spineNamed n))
    (fun _ _ ba sp nm => ba sp nm)
    (fun f args rets sp nm => p sp nm (.call f args rets))
    (fun c f args sp nm => p sp nm (.callIf c f args))
    (fun x fs args rets sp nm => p sp nm (.dispatch x fs args rets))
    (fun _ _ _ => true)
    (fun _ _ => true)
    (fun _ _ b bs sp nm => b sp nm && bs sp nm)
    (fun _ _ => true)
    (fun a _ ba bas sp nm => ba (sp ++ spine a) (nm ++ spineNamed a) && bas sp nm) ss

/-- `callsSpS` of arms. -/
noncomputable def callsSpA (p : List Atom → List V → Stmt → Bool) (as : List (List Stmt)) : List Atom → List V → Bool :=
  Stmt.rec_2 (motive_1 := fun _ => List Atom → List V → Bool) (motive_2 := fun _ => List Atom → List V → Bool)
    (motive_3 := fun _ => List Atom → List V → Bool)
    (fun _ _ _ => true)
    (fun _ z n bz bn sp nm => bz (sp ++ spine z) (nm ++ spineNamed z) && bn (sp ++ spine n) (nm ++ spineNamed n))
    (fun _ _ ba sp nm => ba sp nm)
    (fun f args rets sp nm => p sp nm (.call f args rets))
    (fun c f args sp nm => p sp nm (.callIf c f args))
    (fun x fs args rets sp nm => p sp nm (.dispatch x fs args rets))
    (fun _ _ _ => true)
    (fun _ _ => true)
    (fun _ _ b bs sp nm => b sp nm && bs sp nm)
    (fun _ _ => true)
    (fun a _ ba bas sp nm => ba (sp ++ spine a) (nm ++ spineNamed a) && bas sp nm) as

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
def armsFit (tbl : List (String × ℕ × Bool × Option (Option ℕ))) (sizes : List ℕ) : List String → ℕ → Bool
  | [], _ => true
  | f :: fs, j => (match calFind tbl f with
      | some (m, lp, _) => sizes[j]? == some m && !lp
      | none => false) && armsFit tbl sizes fs (j + 1)

/-- **A frame hint fits a call statement at its site.** -/
noncomputable def frFits (X : AlignCtx) (n : ℕ) (ps : List V) (sp : List Atom) (nm : List V)
    (tbl : List (String × ℕ × Bool × Option (Option ℕ))) : Prover.Exec.Hint → Stmt → Bool
  | .alloc _ m, .call f args _ => match calFind tbl f with
    | some (k, lp, en) => (k == m && !lp) || (lp && match en, args with
      | some (some K), a0 :: _ => (spConst sp a0 0 && Nat.blt 0 K && (K + 1) * k == m) ||
          (spConst sp a0 1 && Nat.blt 1 K && K * k == m)
      | _, _ => false)
    | none => false
  | .allocArm _ sel sizes, .dispatch x fs _ _ =>
      X.locAt x.idx == sel && allocCellOk X n x &&
        ((ps.contains x && (X.extra.lookup x.idx).isNone) || sp.any (fun a ↦ (atomUses a).contains x) ||
          nm.contains x) &&
        Nat.blt sizes.length (2 ^ 28) && armsFit tbl sizes fs 0
  | .allocFrames _ size stop si tail, .callIf b f (a0 :: a1 :: _) => match calFind tbl f with
    | some (k, lp, en) => lp && en == some none && k == size && tail == size && X.locAt a1.idx == stop && allocCellOk X n a1 &&
        ((spConst sp a0 0 && si == 1 && guardOk sp b a1 0) || (spConst sp a0 1 && si == gInv && guardOk sp b a1 1))
    | none => false
  | _, _ => false

/-- **The frame hints' sizes check** of a function: its context, frame size, listed callees, the
offsets of the frame hints it skips, body and advice. -/
noncomputable def frChk (X : AlignCtx) (n : ℕ) (cs skip : List ℕ) (ps : List V) (body : List Stmt)
    (d : ℕ × ℕ × List (ℕ × List Prover.Exec.Hint)) : Bool :=
  (frames X d).isEmpty || (cs.all (fun c ↦ Nat.ble 1 c && Nat.blt c nFns) &&
    callsSpL (fun sp nm st ↦ (frames X d).all fun q ↦ skip.contains q.1 || match allocPtr q.2 with
      | some p => (X.siteAt p (stArgs st) (stRets st)).isNone || frFits X n ps sp nm (calTbl cs) q.2 st
      | none => true) body (spine body) (spineNamed body))

end

end LeanVM.Guest.Bridge
