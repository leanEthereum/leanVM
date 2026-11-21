import LeanVM.Guest.B1.Merkle.CapLinks
import LeanVM.Guest.B1.Sig.SpWotsRef
import LeanVM.Guest.B1.Sig.SpWotsCompleteStmt
import LeanVM.Guest.Ref.KeccakCells

/-!
# The link check rejects

`Linked` (`LeanVM.Guest.Ref.Link`) is `false` on a core function and a reference function that
differ: `verify_merkle_cap__L2` against the reference function at another depth, with a read
dropped, with a hash's input cells swapped, with one name for two cells, and with the branch's
blocks exchanged; `verify_merkle_cap__L4` against it without the zero branch's pins. A miniature
with an assertion, a range check, a `KECCAK` and a `match` against its reference function: its
mutants (the arms exchanged, dropped or repeated, the scrutinee, the range check's bound and
operands, the assertion dropped or changed, a `KECCAK`'s layout flags, read cells and outputs, a
wrong map, two owners of one name, a core assignment added, a value read after the join that
defines it in one arm or block, a value not `V.n k`), a name pinned at a value that does not own
it, the changes the check accepts, and the check in pieces with wrong cuts and boundaries.
`keccak_cells` of nine cells into two (`spongeTo`) is linked to its compiled form, whose second
block reads the state's cells where the padding is zero, and not to that form with a zero cell
added or its outputs swapped.
`sp_wots`'s meaning (`MeaningSpWots`) rejects arguments of the wrong shape and a fourth word whose
digits do not sum to `128`, and its completeness contract's hypotheses are satisfiable.
-/

namespace LeanVMTests.Guest.RefLink

open LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.Ref

/-- `verify_merkle_cap__L2`, the function the mutants are checked against. -/
noncomputable abbrev f := Fn.«verify_merkle_cap__L2».core

example : Linked f (capRef 2) = true := by decide +kernel

example : Linked f (capRef 3) = false := by decide +kernel

/-- The reference function at depth `d` (2 unless given), its commands changed by `g`. -/
def mutant (g : List (Cmd CapName) → List (Cmd CapName)) (d : ℕ := 2) : Func CapName :=
  { capRef d with body := g (capRef d).body }

/-- A name moved by `r` in a term. -/
def renameTm (r : CapName → CapName) : Tm CapName → Tm CapName
  | .v x => .v (r x)
  | .const w => .const w
  | .add a b => .add (renameTm r a) (renameTm r b)
  | .mul a b => .mul (renameTm r a) (renameTm r b)

/-- A command changed where it stands at the top of the body. -/
def mapCmd (g : Cmd CapName → Cmd CapName) : List (Cmd CapName) → List (Cmd CapName) := List.map g

example : Linked f (mutant List.tail) = false := by decide +kernel

example : Linked f (mutant (mapCmd fun
    | .hash2 l0 l1 r0 r1 o0 o1 => .hash2 r0 r1 l0 l1 o0 o1
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (mapCmd fun
    | .load d p off => .load (renameTm (fun x => if x = .runs 1 then .runs 0 else x) d) p off
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (mapCmd fun
    | .ifNz c z n => .ifNz c n z
    | c => c)) = false := by decide +kernel

example : Linked Fn.«verify_merkle_cap__L4».core (mutant (mapCmd fun
    | .ifNz c _ n => .ifNz c [] n
    | c => c) 4) = false := by decide +kernel

/-! ## Assertions, range checks, `KECCAK` and `match` -/

namespace Mini

open LeanVM.Guest.Core

/-- The names of a function `(a, b)`: a hinted `x` with `log x < 2`, `m` the argument it selects,
`o` the first cell of a `KECCAK` of `m` and `a`, asserted to be `b`. -/
inductive N where
  | a | b | x | y | t1 | t2 | m | o
  deriving DecidableEq

instance : Coded N where
  code n := match n with
    | .a => 0 | .b => 1 | .x => 2 | .y => 3 | .t1 => 4 | .t2 => 5 | .m => 6 | .o => 7

/-- The core function. -/
def f : Fn where
  name := "mini"
  params := [.n 0, .n 1]
  body := [.atom (.hint (.witness "w" (.stack [.n 2]))), .atom (.const (.n 3) (word 2 0)),
    .atom (.rangeCheck (.n 2) (.n 4) (.n 5) (.n 6) (.n 3)),
    .match_ (.n 2) [[.atom (.copy (.n 7) (.n 0))], [.atom (.copy (.n 7) (.n 1))]],
    .atom (.keccak (.n 7 :: List.replicate 12 (.n 0)) [.n 8] false false),
    .atom (.assertEq (.n 8) (.n 1)), .ret [.n 8]]

/-- Its reference function. -/
def r : Func N where
  params := [.a, .b]
  body := [.range (.v .x) (.v .y) (.v .t1) (.v .t2) (.const (word 2 0)),
    .match_ (.v .x) [[.eq (.v .m) (.v .a)], [.eq (.v .m) (.v .b)]],
    .keccak (.v .m :: List.replicate 12 (.v .a)) [.v .o] false false, .eq (.v .o) (.v .b)]
  rets := [.v .o]

/-- `r`, its commands changed by `g`. -/
def mutant (g : List (Cmd N) → List (Cmd N)) : Func N := { r with body := g r.body }

/-- `f`, its body changed by `g`. -/
def fm (g : List Stmt → List Stmt) : Fn := { f with body := g f.body }

/-- The inferred map. -/
def m : Map N := infer f r

example : Linked f r = true := by decide +kernel

example : ownersAt m [(2, .x), (7, .m)] = true := by decide +kernel

example : ownersAt m [(7, .x)] = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .match_ c [z, n] => .match_ c [n, z]
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .match_ c [z, _] => .match_ c [z]
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .match_ c [z, n] => .match_ c [z, n, n]
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .match_ _ as => .match_ (.v .a) as
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .range x y t1 t2 _ => .range x y t1 t2 (.const (word 4 0))
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .range x y t1 t2 k => .range y x t1 t2 k
    | c => c)) = false := by decide +kernel

example : Linked f (mutant List.dropLast) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .keccak ins outs i _ => .keccak ins outs i true
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .keccak (i :: ins) outs a b => .keccak (i :: ins.map fun _ => .v .b) outs a b
    | c => c)) = false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .keccak ins outs a b => .keccak ins (outs ++ outs) a b
    | c => c)) = false := by decide +kernel

example : ({ ent := m.ent.set 7 (.v .m, false) } : Map N).check f r = false := by decide +kernel

example : ({ ent := m.ent.set 3 (.const (word 4 0), false) } : Map N).check f r = false := by
  decide +kernel

/-- A core `const` before the `ret`, pinning the parameter `a`. -/
example : Linked (fm fun b => b.take 6 ++ [.atom (.const (.n 0) (word 7 0))] ++ b.drop 6) r =
    false := by decide +kernel

example : Linked f (mutant (List.map fun
    | .keccak ins outs _ o => .keccak ins outs true o
    | c => c)) = false := by decide +kernel

/-- The assertion's second operand changed. -/
example : Linked f (mutant (List.map fun
    | .eq x _ => .eq x (.v .a)
    | c => c)) = false := by decide +kernel

/-- A hint at value `k`. -/
def hintS (k : Nat) : Stmt := .atom (.hint (.witness "w" (.stack [.n k])))

/-- Two values owning one name: `two` returns any two words, its reference function two equal
ones. -/
def two : Fn := ⟨"two", [.n 0], [hintS 1, hintS 2, .ret [.n 1, .n 2]]⟩

example : (⟨[(.v .a, true), (.v .x, true), (.v .x, true)]⟩ : Map N).check two
    ⟨[.a], [], [.v .x, .v .x]⟩ = false := by decide +kernel

/-- A value defined in one arm of a `match`, or one block of a branch, read after the join. -/
example : Linked ⟨"arm", [.n 0], [.match_ (.n 0) [[.atom (.const (.n 1) (word 1 0))], []],
    .ret [.n 1]]⟩ (⟨[.a], [.match_ (.v .a) [[], []]], [.const (word 1 0)]⟩ : Func N) = false := by
  decide +kernel

example : Linked ⟨"ite", [.n 0], [.ite (.n 0) [.atom (.const (.n 1) (word 1 0))] [],
    .ret [.n 1]]⟩ (⟨[.a], [.ifNz (.v .a) [] []], [.const (word 1 0)]⟩ : Func N) = false := by
  decide +kernel

/-- A core value that is not `V.n k`. -/
example : Linked ⟨"tag", [.n 0], [.ret [⟨[], 1, 0⟩]]⟩ (⟨[.a], [], [.v .a]⟩ : Func N) = false := by
  decide +kernel

/-- A hint first read by an assertion is named there. -/
example : Linked ⟨"assert", [.n 0], [hintS 1, .atom (.assertEq (.n 1) (.n 0)), .ret [.n 1]]⟩
    (⟨[.a], [.eq (.v .x) (.v .a)], [.v .x]⟩ : Func N) = true := by decide +kernel

/-! Accepted, and equal in meaning: the range check's two read words exchanged (both are names
the check binds), the hint dropped (it constrains nothing), statements after the `ret`. -/

example : Linked f (mutant (List.map fun
    | .range x y t1 t2 k => .range x y t2 t1 k
    | c => c)) = true := by decide +kernel

example : Linked (fm List.tail) r = true := by decide +kernel

example : Linked (fm (· ++ [.atom (.const (.n 9) (word 7 0))])) r = true := by decide +kernel

/-! ## In pieces -/

/-- The known values after the parameters. -/
def K0 : Nat := (m.uses 0 f.params).getD 0

/-- The body cut after the range check, the commands after theirs. -/
def P : List (List Stmt) := cutAt [3] f.body
def Q : List (List (Cmd N)) := cutAt [1] r.body

example : (m.segOk K0 15 (P.getD 0 []) (Q.getD 0 []) &&
    m.body 15 (P.getD 1 []) (Q.getD 1 []) r.rets) = true := by decide +kernel

/-- A boundary claiming value `7` known, which the first piece does not define. -/
example : m.segOk K0 255 (P.getD 0 []) (Q.getD 0 []) = false := by decide +kernel

/-- The commands cut one late, and one early. -/
example : m.segOk K0 15 (P.getD 0 []) ((cutAt [2] r.body).getD 0 []) = false := by decide +kernel

example : m.segOk K0 15 (P.getD 0 []) ((cutAt [0] r.body).getD 0 []) = false := by decide +kernel

/-- The body cut one late. -/
example : m.segOk K0 15 ((cutAt [4] f.body).getD 0 []) (Q.getD 0 []) = false := by decide +kernel

/-- A function whose second piece reads a value the boundary drops: defined, but not an owner. -/
def f2 : Fn where
  name := "mini2"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 3) (word 2 0)), .atom (.hint (.witness "w" (.stack [.n 2]))),
    .atom (.rangeCheck (.n 2) (.n 4) (.n 5) (.n 6) (.n 3)), .ret [.n 2]]

/-- Its reference function. -/
def r2 : Func N where
  params := [.a, .b]
  body := [.range (.v .x) (.v .y) (.v .t1) (.v .t2) (.const (word 2 0))]
  rets := [.v .x]

example : Linked f2 r2 = true := by decide +kernel

example : (infer f2 r2).segOk 3 3 ((cutAt [1] f2.body).getD 0 []) [] = true := by decide +kernel

example : (infer f2 r2).body 3 ((cutAt [1] f2.body).getD 1 []) r2.body r2.rets = false := by
  decide +kernel

end Mini

/-! ## `keccak_cells` into two cells -/

namespace Sponge

open LeanVM.Guest.Core

/-- The names: the argument, nine message cells, the state before block `b`, the two outputs. -/
inductive SN where
  | a
  | msg (i : ℕ)
  | st (b c : ℕ)
  | o (j : ℕ)
  deriving DecidableEq

instance : Coded SN where
  code n := match n with
    | .a => 0 | .msg i => 3 * i + 1 | .st b c => 3 * (13 * b + c) + 2 | .o j => 3 * j + 3

/-- `keccak_cells(msg, out)`, nine hinted cells into two, compiled: block `1` XORs cells `0`, `1`
and `8` (the message's last cell, the padding's `0x01` and `0x80`) and reads cells `2` to `7`. -/
def f (zero : List Stmt := []) (c2 : V := .n 14) : Fn where
  name := "sponge"
  params := [.n 0]
  body := [.atom (.hint (.witness "w" (.stack ((List.range 9).map (.n <| · + 1))))),
    .atom (.const (.n 10) (word 1 0)), .atom (.const (.n 11) (word 0 0)),
    .atom (.keccak ((List.range 9).map (.n <| · + 1) ++ List.replicate 4 (.n 11))
      ((List.range 13).map (.n <| · + 12)) false true),
    .atom (.add (.n 25) (.n 12) (.n 9)), .atom (.add (.n 26) (.n 13) (.n 10)),
    .atom (.const (.n 27) (word 0 9223372036854775808)), .atom (.add (.n 28) (.n 20) (.n 27))] ++
    zero ++
    [.atom (.keccak ([.n 25, .n 26, c2] ++ (List.range 5).map (.n <| · + 15) ++
      .n 28 :: (List.range 4).map (.n <| · + 21)) [.n 29, .n 30] true false),
    .ret [.n 29, .n 30]]

/-- Its reference function, the outputs `o0`, `o1`. -/
def r (o0 : Tm SN := .v (.o 0)) (o1 : Tm SN := .v (.o 1)) : Func SN where
  params := [.a]
  body := spongeTo (fun b c => .v (.st b c)) ((List.range 9).map (.v <| .msg ·)) 9 o0 o1
  rets := [.v (.o 0), .v (.o 1)]

example : Linked (f) r = true := by decide +kernel

/-- Cell `2` of block `1` XORed with the zero padding cell. -/
example : Linked (f [.atom (.add (.n 31) (.n 14) (.n 11))] (.n 31)) r = false := by decide +kernel

example : Linked (f) (r (.v (.o 1)) (.v (.o 0))) = false := by decide +kernel

end Sponge

/-! ## `sp_wots`'s meaning is not vacuous -/

namespace SpWots

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1.Sig
open LeanVM.Protocol.Verifier

example (rd : Reader) : ¬ MeaningSpWots rd [] [] := by
  rintro ⟨_, _, _, _, _, h, -⟩
  simp at h

/-- A zero fourth word encodes digits of sum `0`, not `128`. -/
example (rd : Reader) (pp a0 a1 l : E) : ¬ MeaningSpWots rd [pp, a0, a1, 0] [l] := by
  rintro ⟨_, _, _, d, _, h, -, hd, hsum, -⟩
  have h0 : (0 : E) = eOfNat128 (spX d 64) := (List.cons.inj (List.cons.inj (List.cons.inj
    (List.cons.inj h).2).2).2).1
  let d' : ℕ → ℕ := fun j => if j < 64 then d j else 0
  have hd' : ∀ j, d' j < 4 := fun j => by
    simp only [d']; split_ifs with hj; exacts [hd j hj, by norm_num]
  have hx : spX d 64 = spX d' 64 := spX_congr fun i hi => by simp [d', hi]
  have e := congrArg eToNat h0
  rw [← eOfNat128_zero, eToNat_eOfNat128, eToNat_eOfNat128, hx,
    Nat.mod_eq_of_lt (spX_lt hd' le_rfl)] at e
  have hz : ∀ i ∈ Finset.range 64, d i = 0 := fun i hi => by
    have hi := Finset.mem_range.mp hi
    rw [show d i = d' i by simp [d', hi], ← spX_digit hd' hi, ← e]
    simp
  rw [Finset.sum_congr rfl hz] at hsum
  simp at hsum

/-- The completeness contract's hypotheses hold of the digits all `2`. -/
example {C : CallRel} {rd : Reader} (hm : MemOK rd 64) :
    ∃ σ : Val, σ (.n 0) = 0 ∧ σ (.n 1) = 0 ∧ σ (.n 2) = 0 ∧
      σ (.n 3) = eOfNat128 (spX (fun _ => 2) 64) ∧
      Stmt.HoldsList C rd σ (Fn.«sp_wots».core).body False
        (fun rs => rs = [spLeafCell 0 0 0 (fun _ => 2) fun _ => 0]) :=
  sp_wots_complete_cells (fun _ => by norm_num) (by simp) hm

end SpWots

end LeanVMTests.Guest.RefLink
