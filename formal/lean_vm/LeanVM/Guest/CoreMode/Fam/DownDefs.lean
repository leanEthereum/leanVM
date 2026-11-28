/-
  LeanVM.Guest.CoreMode.Fam.DownDefs

  The facts carried to callees, every family's check of one function in one walk of its body at the generator's hints
  (`downH`): what `Gen/Down*` evaluate. Their soundness is `Fam/ResDown.lean`.
-/

module

public import LeanVM.Guest.CoreMode.Fam.TabDefs
public import LeanVM.Guest.CoreMode.Fam.CarryDefs
public import LeanVM.Guest.CoreMode.Fam.ExpCDefs
public import LeanVM.Guest.CoreMode.Fam.LinkDefs

/-!
# The facts carried to callees, in one walk

The families' checks (the carried and nonzero facts `Res.carryG`, `Res.carryNzG`, the exponent bounds
`CoreMode.carryExpB`, the callers' `Res.callersG`, `Res.callersM`, `Res.callersB`) each walk a whole body and search
its whole spine. `downH` walks it once (`allB`), at the generator's hints (`DownHints`, `Fam/TabDefs.lean`): each
search over the sub-spine the hints name, each list of names read through its table (`DownT`, each table pinned to its
list by `tabOk`). At an atom it checks the carried facts' heap witness and a dynamic allocation's size, at a call site
each family's site check (`siteD`), the callee's code computed once.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Bridge (spine)
open LeanVM.Guest.Exec (natSeq)

@[expose] public section

/-! ## Each family's checks at the hints -/

/-- `selTabB` over a spine and selectors. -/
noncomputable def selTabS (sp : List Ev) (sels : List (V × ℕ)) (v : V) : Bool :=
  sp.any fun
    | .atom (.load d p off) => veq d v && sp.any (fun
        | .atom (.mul q a b) => veq q p && (selTabAt sp sels a b off || selTabAt sp sels b a off)
        | _ => false)
    | _ => false

/-- `kvNz` by the tables of `carriedNz` and `ownNz`. -/
def kvNzH (T O : NTab ℕ) (fn : Fn) : List V :=
  ((T.at (encS fn.name)).filterMap fun i ↦ fn.params[i]?) ++ (if fn.loop then fn.params.take 1 else []) ++
    (O.at (encS fn.name)).map V.n

/-- `upChk` over a sub-spine. -/
noncomputable def upChkH (fn : Fn) (sp : List Ev) (i : ℕ) : Bool :=
  match fn.params[i]? with
  | some p => nzOf [] sp nzDepth p
  | none => allB (fun _ s ↦ retNz (i - fn.params.length) sp s) fn.body (spineE fn.body)

/-- `ownChk` over a sub-spine, the table read first. -/
noncomputable def ownChkH (fn : Fn) (sp : List Ev) (v : V) : Bool :=
  selTabS sp (topSelsC fn.body) v || armNzB v fn.body

/-- `pin` over a sub-spine. -/
noncomputable def pinH (fn : Fn) (sp : List Atom) : Kd → V → Bool
  | .inK, v => kOf (cvars fn .inK) sp kDepth v
  | .tab, v => pin fn .tab v

/-- **`siteC` by the table of `carried`**, over a sub-spine, `c` the callee's code. -/
noncomputable def siteCH (T : NTab (ℕ × Kd)) (fn : Fn) (sp : List Atom) (c : ℕ) (args : List V) : Bool :=
  (T.at c).all fun e ↦ match args[e.1]? with
    | some a => pinH fn sp e.2 a
    | none => false

/-- **`siteNz` by the table of `carriedNz`**, over a sub-spine, `c` the callee's code. -/
noncomputable def siteNzH (T : NTab ℕ) (kv : List V) (sp : List Ev) (c : ℕ) (args : List V) : Bool :=
  (T.at c).all fun i ↦ match args[i]? with
    | some a => nzOf kv sp nzDepth a
    | none => false

/-- **`carryExpB`'s check of a site by the table of its list**, over a sub-spine, `c` the callee's code. -/
noncomputable def siteExpH (T : NTab (ℕ × ℕ × ℕ)) (fn : Fn) (sp : List Ev) (c : ℕ) (args : List V) : Bool :=
  (T.at c).all fun e ↦ match args[e.1]? with
    | some a => CoreMode.constExpS a e.2.1 e.2.2 sp || CoreMode.armExpB a e.2.1 e.2.2 fn.body
    | none => false

/-- **`callersG`'s check of a site by the table of its list**: the code `k` of `fn` the code of each caller of the
callee `f` (code `c`), or `fn` is the callee, a loop. -/
noncomputable def siteGH (T : NTab ℕ) (fn : Fn) (k : ℕ) (f : String) (c : ℕ) : Bool :=
  (T.at c).all fun d ↦ Nat.beq d k || (fn.name == f && fn.loop)

/-- **`callersM`'s check of a site by the table of its list**: `k` among the callee's callers' codes, or `fn` the
callee, a loop. -/
noncomputable def siteMH (T : NTab (List ℕ)) (fn : Fn) (k : ℕ) (f : String) (c : ℕ) : Bool :=
  (T.at c).all fun cs ↦ cs.contains k || (fn.name == f && fn.loop)

/-- **`callersB`'s check of a site by the table of its link's callees**: the callee not linked, or `k` the caller's
code `o`, or `fn` the callee, a loop. -/
noncomputable def siteBH (T : NTab Unit) (o : ℕ) (fn : Fn) (k : ℕ) (f : String) (c : ℕ) : Bool :=
  (T.at c).isEmpty || Nat.beq k o || (fn.name == f && fn.loop)

/-! ## Every family in one walk -/

/-- **The tables the families read**, each pinned to its list by `tabOk` (`Gen/DownTab.lean`), and the code of the
linked callees' caller. -/
structure DownT where
  carried : NTab (ℕ × Kd)
  cnz : NTab ℕ
  up : NTab ℕ
  own : NTab ℕ
  exp : NTab (ℕ × ℕ × ℕ)
  term : NTab ℕ
  gl : NTab (List ℕ)
  mono : NTab ℕ
  any : NTab Unit
  anyO : ℕ

/-- **A function's hints**: the sub-spines of the carried facts' searches (over `Bridge.spine`), of the nonzero facts'
and of the exponent bounds' (over `Memory.spineE`), each a bitset. -/
structure DownHints where
  g : ℕ
  nz : ℕ
  exp : ℕ

/-- **Every family's check of a call site**, `k` the caller's code, `c` the callee's. -/
noncomputable def siteD (D : DownT) (fn : Fn) (spA : List Atom) (kv : List V) (spN spX : List Ev) (k : ℕ) (f : String)
    (args : List V) (c : ℕ) : Bool :=
  siteCH D.carried fn spA c args && siteNzH D.cnz kv spN c args && siteExpH D.exp fn spX c args &&
    siteGH D.term fn k f c && siteMH D.gl fn k f c && siteGH D.mono fn k f c && siteBH D.any D.anyO fn k f c

/-- A dynamic allocation's size nonzero in `K`. -/
noncomputable def nzAtom (kv : List V) (sp : List Ev) : Atom → Bool
  | .hint (.allocDyn _ s) => nzOf kv sp nzDepth s
  | _ => true

/-- **Every family's check of a statement**: an atom's (a heap witness, a dynamic allocation's size), a call site's
(`siteD`, the callee's code evaluated first). -/
noncomputable def stmtD (D : DownT) (fn : Fn) (spA : List Atom) (kv : List V) (spN spX : List Ev) (k : ℕ) :
    Stmt → Bool
  | .atom a => witAtomC fn spA a && nzAtom kv spN a
  | .call f args _ => natSeq (encS f) (siteD D fn spA kv spN spX k f args)
  | .callIf _ f args => natSeq (encS f) (siteD D fn spA kv spN spX k f args)
  | .dispatch _ fs args _ => fs.all fun f ↦ natSeq (encS f) (siteD D fn spA kv spN spX k f args)
  | _ => true

/-- **The facts carried to callees, every family's check of one function**, at its hints `w`. -/
noncomputable def downH (D : DownT) (fn : Fn) (w : DownHints) : Bool :=
  natSeq (encS fn.name) fun k ↦
    allB (fun _ s ↦ stmtD D fn (pickB w.g (spine fn.body)) (kvNzH D.cnz D.own fn) (pickB w.nz (spineE fn.body))
      (pickB w.exp (spineE fn.body)) k s) fn.body (spineE fn.body) &&
    (D.up.at k).all (upChkH fn (pickB w.nz (spineE fn.body))) &&
    (D.own.at k).all fun v ↦ ownChkH fn (pickB w.nz (spineE fn.body)) (V.n v)

end

end LeanVM.Guest.Res
