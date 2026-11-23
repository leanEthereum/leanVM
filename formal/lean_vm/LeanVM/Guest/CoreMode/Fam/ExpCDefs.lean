/-
  LeanVM.Guest.CoreMode.Fam.ExpCDefs

  Values a body pins to powers of `g` on every returning path, read off its code, and the parameters
  whose exponent bounds every call site carries down.
-/

module

public import LeanVM.Guest.CoreMode.Fam.ExpDefs

/-!
# Exponents a body pins, carried down

`valExpB body v lo hi`: on every returning path, `v` is `g^e`, `lo ≤ e < hi`: a `const` of the body's spine (`constExpS`),
or a copy of such a constant on the spine of every arm of a top-level `match` before any statement that may return
(`armExpB`, the values a `match` binds per arm, as `open_stacked`'s `level_rate`). `carryExpB L fn`: every call site of
`fn` passes each listed callee `(callee, parameter, lo, hi)` an argument `fn` pins so (`Fam/ResExpC.lean`: every honest
instance of the callee then has its parameter's word `g^e`, `lo ≤ e < hi`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- **A spine pins `v` to a constant `g^e`, `lo ≤ e < hi`**: a `const` atom of `v`. -/
noncomputable def constExpS (v : V) (lo hi : ℕ) (sp : List Ev) : Bool :=
  sp.any fun
    | .atom (.const d w) => Res.veq d v && (Res.powOf1 w).any fun e ↦ Nat.ble lo e && Nat.blt e hi
    | _ => false

/-- **A spine pins `v` by a copy** of a constant it pins so (`constExpS`). -/
noncomputable def copyExpS (v : V) (lo hi : ℕ) (sp : List Ev) : Bool :=
  sp.any fun
    | .atom (.copy d s) => Res.veq d v && constExpS s lo hi sp
    | _ => false

/-- **`v` copied from a constant `g^e`, `lo ≤ e < hi`, on the spine of every arm of a top-level `match`**, before any
statement that may return. -/
noncomputable def armExpB (v : V) (lo hi : ℕ) : List Stmt → Bool
  | [] => false
  | s :: ss => (match s with
      | .match_ _ (a :: as) => (a :: as).all fun b ↦ copyExpS v lo hi (spineE b)
      | _ => false) || (Bridge.noRet [s] && armExpB v lo hi ss)

/-- **`v` is `g^e`, `lo ≤ e < hi`, on every returning path of `body`**: a constant of its spine, or `armExpB`. -/
noncomputable def valExpB (body : List Stmt) (v : V) (lo hi : ℕ) : Bool :=
  constExpS v lo hi (spineE body) || armExpB v lo hi body

/-- **Every call site of `fn` carries the listed parameters' bounds**: for each `(callee, parameter, lo, hi)` of `L`, a
call of the callee passes at that parameter a value `fn` pins to `g^e`, `lo ≤ e < hi` (`valExpB`). -/
noncomputable def carryExpB (L : List (String × ℕ × ℕ × ℕ)) (fn : Fn) : Bool :=
  Res.sitesB (fun f args _ ↦ L.all fun c ↦ c.1 != f || match args[c.2.1]? with
    | some a => valExpB fn.body a c.2.2.1 c.2.2.2
    | none => false) fn.body

end

end LeanVM.Guest.CoreMode
