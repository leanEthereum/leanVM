/-
  The input of `scripts/b2-residual`: the back end's places of the guest's values compared with
  the certificates' cells (`B2.Agree.fnOk`), run with `lake env lean --run` on a file of the
  certificates' cells (one line per function: its name, then its cells).
-/
import LeanVM.Guest.Data.Source
import LeanVM.Guest.Backend.ExpandTrace
import LeanVM.Guest.Renumber
import LeanVM.Guest.Backend.Guest.Traced
import LeanVM.Guest.Backend.Guest.B2.Agree

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Backend LeanVM.Guest.Backend.B2

mutual
/-- The constant atoms of a statement the comparison without residual entries rejects. -/
partial def failS (A : Agree) (known : List (Nat × Nat × Nat)) : Stmt → List (V × LeanVM.Parameters.E)
  | .atom (.const v c) => if A.atomOk known (.const v c) then [] else [(v, c)]
  | .ite _ z n => failL A known z ++ failL A known n
  | .match_ _ arms => arms.flatMap (failL A known)
  | _ => []

/-- The rejected constant atoms of a block. -/
partial def failL (A : Agree) (known : List (Nat × Nat × Nat)) : List Stmt → List (V × LeanVM.Parameters.E)
  | [] => []
  | s :: ss => failS A known s ++ failL A (A.after known s) ss
end

/-- The residual entries of a function: the pointers placed shifted whose cells differ, and the
constants whose cells no earlier constant on the path set. -/
def residualOf (A : Agree) (f : Fn) : List (V × Res) :=
  let vs := f.params ++ Stmt.valsList f.body
  let addrs := (vs.filterMap fun v => if A.eqv v then none else match A.pl v with
    | some (.shifted n e) => some (v, Res.addr n e)
    | _ => none).foldl (fun acc p => if acc.contains p then acc else acc ++ [p]) []
  addrs ++ (failL A [] f.body).map fun (v, c) => (v, .konst (limbsOf c).1 (limbsOf c).2)

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: b2-residual.lean CELLS"; return 1
  let text ← IO.FS.readFile path
  let cells : Std.HashMap String (List Nat) := text.splitOn "\n" |>.foldl (init := {}) fun m l =>
    match l.splitOn " " with
    | name :: ns => if name.isEmpty then m else m.insert name (ns.filterMap String.toNat?)
    | [] => m
  match ExpandTrace.expandProgram Data.guest with
  | .error e => IO.eprintln e; return 1
  | .ok P =>
    let core := (P.map (·.core)).map Fn.renumber
    let tr : List TracedFn :=
      (core.zip GuestData.guestInfo).map fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
    match placeProgram tr with
    | .error e => IO.eprintln s!"placement: {e}"; return 1
    | .ok (pl, _) =>
      let mut failed := 0
      let mut nres := 0
      for ((pf, tf), i) in (pl.zip tr).zipIdx do
        let f := tf.core
        let cl := cells.getD f.name []
        let A : Agree := ⟨fun v => pf.locs[v]?, cl, []⟩
        if A.fnOk f then continue
        let res := residualOf A f
        let A' : Agree := { A with res := res }
        if !(A'.fnOk f) then
          failed := failed + 1
          IO.eprintln s!"fails: {f.name}"
        nres := nres + res.length
        let items := res.map fun (v, r) => match r with
          | .konst c0 c1 => s!"(.n {v.idx}, .konst {c0} {c1})"
          | .addr n e => s!"(.n {v.idx}, .addr {n} {e})"
        IO.println s!"res {f.name} {i + 1} {String.intercalate "; " items}"
      IO.println s!"stats: functions {pl.length} residual-values {nres} failing {failed}"
      return (if failed == 0 then 0 else 1)
