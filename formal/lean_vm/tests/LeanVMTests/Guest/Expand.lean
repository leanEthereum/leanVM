import Statement.Data.Bytecode
import LeanVM.Guest.Code
import LeanVM.Guest.Data.Source
import LeanVM.Guest.ExpandLemmas
import LeanVM.Guest.Interp
import LeanVMTests.Guest.Programs

open LeanVM.Parameters LeanVM.Guest LeanVM.Guest.Source LeanVM.Guest.Interp
open LeanVMTests.Guest.Programs

namespace LeanVMTests.Guest.Expand

/-- `g^i ↦ i` below `2^14`, the interpreter's discrete logarithm. -/
def logs : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  let mut x : K := 1
  for i in List.range (2 ^ 14) do
    m := m.insert (keyOf x) i
    x := x * g
  return m

def wordOf (c : Nat × Nat) : E := word c.1 c.2

/-- Expand `p` and run its `main` on the public input `pi` and the witness streams. -/
def runMain (p : Source.Program) (pi : List E) (streams : List (String × List (List E)) := []) :
    Except String Unit := do
  let fns ← Expand.expandProgram p
  let cfg : Cfg := {
    program := fns,
    initMem := fun a => if a == gpowK 0 then pi[0]? else if a == gpowK 1 then pi[1]? else none,
    dlog := fun a => logs[keyOf a]?,
    streams }
  discard <| run cfg "main" []

def runTest (t : TestProgram) (pi : List E) : Except String Unit :=
  runMain t.program pi (t.streams.map fun (s, es) => (s, es.map (·.map wordOf)))

def isOk {α : Type} : Except String α → Bool
  | .ok _ => true
  | .error _ => false

/-! ## The compiler's test programs

Every `crates/lean_compiler/tests/programs/*.py`, which the Rust prover proves and verifies on its
annotated public input, expands and runs on it; changing the first public word makes every
program that publishes one fail. -/

#guard LeanVMTests.Guest.Programs.all.all fun t => isOk (runTest t (t.publicInput.map wordOf))

#guard (LeanVMTests.Guest.Programs.all.filter (·.name != "identities")).all fun t =>
  let pi := t.publicInput.map wordOf
  !isOk (runTest t [pi[0]! + 1, pi[1]!])

def showProgram (p : Source.Program) : String :=
  match Expand.expandProgram p with
  | .ok fns => String.intercalate "\n" (fns.map showFn)
  | .error e => e

/-- info: def main():
  hint %s0#0 = HeapBuf(12)
  %s1#0 = 1
  %s1#0 = mem[%s0#0 g^0]
  %s2#0 = 2
  %s2#0 = mem[%s0#0 g^1]
  %s3#0 = 1
  [] = __loop0(%s3#0, %s0#0)
  %s4#0 = mem[%s0#0 g^11]
  %s5#0 = 905969664
  assert %s4#0 == %s5#0
  %s6#0 = 9223372036854775983
  assert log %s4#0 < log g*%s6#0 by %s6#1, %s6#2, %s6#3
  %s8#0 = 1
  %s4#0 = mem[%s8#0 g^0]
  %s9#0 = 1
  %s9#1 = 2
  %s9#2 = %s9#0 * %s9#1
  %s4#0 = mem[%s9#2 g^0]
  return
def __loop0(%#0, %#0[1]):
  %s0#0 = %#0[1] * %#0
  %s0#1 = mem[%s0#0 g^0]
  %s0#2 = %#0[1] * %#0
  %s0#3 = mem[%s0#2 g^1]
  %s0#4 = %s0#1 * %s0#3
  %s0#5 = %#0[1] * %#0
  %s0#4 = mem[%s0#5 g^2]
  %s2#0 = 2
  %s2#1 = %#0 * %s2#0
  %s2#2 = 1024
  %s2#3 = %s2#1 + %s2#2
  %s2#4 = 2
  %s2#5 = %#0 * %s2#4
  if %s2#3 != 0: __loop0(%s2#5, %#0[1])
  return -/
#guard_msgs in
#eval IO.println (showProgram prog_fibonacci.program)
/-- info: def main():
  hint %s0#0 = HeapBuf(4)
  %s1#0 = 5
  %s1#0 = mem[%s0#0 g^0]
  %s2#0 = 7
  %s2#0 = mem[%s0#0 g^1]
  %s3#0 = 11
  %s3#0 = mem[%s0#0 g^2]
  %s4#0 = 13
  %s4#0 = mem[%s0#0 g^3]
  [%s5#0, %s5#1] = hash_pair__L0(%s0#0)
  %s7#1 = 2
  [%s7#0, %s7#0[1]] = match log %s7#1: hash_pair__L0 | hash_pair__L1(%s0#0)
  %s9#0 = %s5#0 + %s7#0
  %s9#1 = 1
  %s9#0 = mem[%s9#1 g^0]
  %s10#0 = %s5#1 + %s7#0[1]
  %s10#1 = 1
  %s10#2 = 2
  %s10#3 = %s10#1 * %s10#2
  %s10#0 = mem[%s10#3 g^0]
  return
def hash_pair__L0(%#0):
  %s1#0 = mem[%#0 g^0]
  %s1#0[1] = mem[%#0 g^1]
  %s1#1 = mem[%#0 g^0]
  %s1#1[1] = mem[%#0 g^1]
  %s1#2 = 1
  %s1#2[1] = 0
  %s1#2[2] = 0
  %s1#2[3] = 0
  %s1#2[4] = 0
  %s1#3 = 9223372036854775808
  [%s0#0, %s0#0[1]] even = keccak_f([%s1#0, %s1#0[1], %s1#1, %s1#1[1], %s1#2, %s1#2[1], %s1#2[2], %s1#2[3], %s1#3, %s1#2[1], %s1#2[2], %s1#2[3], %s1#2[4]] even)
  %s2#0 = %s0#0
  %s2#0[1] = %s0#0[1]
  return %s2#0, %s2#0[1]
def hash_pair__L1(%#0):
  %s1#0 = mem[%#0 g^2]
  %s1#0[1] = mem[%#0 g^3]
  %s1#1 = mem[%#0 g^2]
  %s1#1[1] = mem[%#0 g^3]
  %s1#2 = 1
  %s1#2[1] = 0
  %s1#2[2] = 0
  %s1#2[3] = 0
  %s1#2[4] = 0
  %s1#3 = 9223372036854775808
  [%s0#0, %s0#0[1]] even = keccak_f([%s1#0, %s1#0[1], %s1#1, %s1#1[1], %s1#2, %s1#2[1], %s1#2[2], %s1#2[3], %s1#3, %s1#2[1], %s1#2[2], %s1#2[3], %s1#2[4]] even)
  %s2#0 = %s0#0
  %s2#0[1] = %s0#0[1]
  return %s2#0, %s2#0[1] -/
#guard_msgs in
#eval IO.println (showProgram prog_const_params.program)

/-! ## Guest functions

`@inline` helpers run through a `main` of their own, on the guest's definitions. -/

/-- A guest function. -/
def guestFn (n : String) : Func := (Data.guest.funcs.find? (·.name == n)).getD default

/-- A statement. -/
def st (k : StmtKind) : Source.Stmt := .mk 0 k

/-- `p = GEN ** 0; p[1] = a; p[GEN] = b`. -/
def publish (a b : Expr) : List Source.Stmt :=
  [st (.let_ "p" (.gpow 0)), st (.store (.var "p") (.lit 1) a), st (.store (.var "p") .gen b)]

/-- A `main` beside these guest functions. -/
def withGuest (fs : List String) (body : List Source.Stmt) : Source.Program :=
  ⟨{ name := "main", params := [], returnShapes := [], body, inline := false } :: fs.map guestFn,
    Data.guest.constArrays⟩

/-- `r = pack64x2(a, b)`, published. -/
def packMain (a b : Expr) : Source.Program :=
  withGuest ["pack64x2"] ([st (.let_ "r" (.call "pack64x2" [a, b]))] ++ publish (.var "r") (.lit 0))

/-- info: def main():
  %s0#1 = 3
  %s0#2 = 5
  assert_in_k %s0#1, %s0#2
  %s0.i3:pack64x2.s1#0 = (0, 1, 0)
  %s0.i3:pack64x2.s1#1 = %s0.i3:pack64x2.s1#0 * %s0#2
  %s0#0 = %s0#1 + %s0.i3:pack64x2.s1#1
  %s2#0 = 1
  %s0#0 = mem[%s2#0 g^0]
  %s3#0 = 0
  %s3#1 = 1
  %s3#2 = 2
  %s3#3 = %s3#1 * %s3#2
  %s3#0 = mem[%s3#3 g^0]
  return -/
#guard_msgs in
#eval IO.println (showProgram (packMain (.lit 3) (.lit 5)))

-- `pack64x2(3, 5)` is `3 + 5·y`; a word outside `K` fails `assert_in_k`.
#guard isOk (runMain (packMain (.lit 3) (.lit 5)) [word 3 5 0, 0])
#guard !isOk (runMain (packMain (.lit 3) (.lit 5)) [word 3 6 0, 0])
#guard !isOk (runMain (packMain (.call "f192" [.lit 0, .lit 1, .lit 0]) (.lit 5)) [word 0 6 0, 0])

/-! ## The Keccak builtins

Each against the Spec: `keccak` and `keccak_cells` compute Keccak-256 of the message's bytes, each
cell its two low limbs as sixteen little-endian bytes (`Protocol.KeccakHash.keccak256`), the
digest in its two cells (`digestHalves`); `state=` continues the sponge where `final=0` left it;
`cap=` is one Keccak-f[1600] on the eight message cells, zero, and the previous output's last five
cells. A wrong digest fails. -/

open LeanVM.Protocol.KeccakHash in
/-- The digest of the first `len` bytes of the cells, as two cells. -/
def cellsDigest (cells : List E) (len : Nat) : List E :=
  let d := keccak256 ((cells.flatMap fun c
      => K.toBytes (c.limb 0) ++ K.toBytes (c.limb 1)).take len)
  [(digestHalves d).1, (digestHalves d).2]

/-- Source literals as words. -/
def lits (ns : List Nat) : List E := ns.map litField

/-- `h = StackBuf(2)`, `stmts`, then `h` published. -/
def hashMain (stmts : List Source.Stmt) : Source.Program :=
  ⟨[{ name := "main", params := [], returnShapes := [], inline := false,
      body := [st (.let_ "h" (.stackBuf 2))] ++ stmts ++
        publish (.index (.var "h") (.lit 0)) (.index (.var "h") (.lit 1)) }], []⟩

/-- A keyword argument. -/
def kw (k : String) (v : Expr) : Expr := .call s!"__kw_{k}" [v]

/-- `keccak([7, 9], [11, 13], h)`. -/
def keccak64 : Source.Program :=
  hashMain [st (.call "keccak" [.list [.lit 7, .lit 9], .list [.lit 11, .lit 13], .var "h"])]

/-- info: def main():
  %s1#0 = 7
  %s1#1 = 9
  %s1#2 = 11
  %s1#3 = 13
  %s1#4 = 1
  %s1#4[1] = 0
  %s1#4[2] = 0
  %s1#4[3] = 0
  %s1#4[4] = 0
  %s1#5 = 9223372036854775808
  [%s0#0, %s0#0[1]] even = keccak_f([%s1#0, %s1#1, %s1#2, %s1#3, %s1#4, %s1#4[1], %s1#4[2], %s1#4[3], %s1#5, %s1#4[1], %s1#4[2], %s1#4[3], %s1#4[4]] even)
  %s3#0 = 1
  %s0#0 = mem[%s3#0 g^0]
  %s4#0 = 1
  %s4#1 = 2
  %s4#2 = %s4#0 * %s4#1
  %s0#0[1] = mem[%s4#2 g^0]
  return -/
#guard_msgs in
#eval IO.println (showProgram keccak64)

#guard isOk (runMain keccak64 (cellsDigest (lits [7, 9, 11, 13]) 64))
#guard !isOk (runMain keccak64 (cellsDigest (lits [7, 9, 11, 14]) 64))

/-- `keccak([7, 9], [11, 0], h, len=48)`, the padding XORed into the message's fourth cell. -/
def keccak48 : Source.Program :=
  hashMain [st (.call "keccak" [.list [.lit 7, .lit 9], .list [.lit 11, .lit 0], .var "h",
    kw "len" (.lit 48)])]

#guard isOk (runMain keccak48 (cellsDigest (lits [7, 9, 11]) 48))
#guard !isOk (runMain keccak48 (cellsDigest (lits [7, 9, 11, 0]) 64))

/-- `a = [3, 4, ..., 9, 0]`, `keccak(a[0:2], a[2:4], h, tail=a[4:8], len=120)`: a `StackBuf`
message ending mid-cell, its `tail` read in place. -/
def keccakTail : Source.Program :=
  hashMain [st (.let_ "a" (.list (((List.range 7).map fun i => .lit (i + 3)) ++ [.lit 0]))),
    st (.call "keccak" [.slice (.var "a") (.lit 0) (.lit 2), .slice (.var "a") (.lit 2) (.lit 4),
      .var "h", kw "tail" (.slice (.var "a") (.lit 4) (.lit 8)), kw "len" (.lit 120)])]

#guard isOk (runMain keccakTail (cellsDigest (lits ((List.range 7).map (· + 3) ++ [0])) 120))
#guard !isOk (runMain keccakTail (cellsDigest (lits ((List.range 7).map (· + 3) ++ [0])) 128))

/-- `[const(j + 1) for j in unroll(lo, hi)]`. -/
def plusOne (lo hi : Nat) : Expr :=
  .listComp (.call "const" [.add (.var "j") (.lit 1)]) "j" (.lit lo) (.lit hi)

/-- `keccak_cells([const(j + 1) for j in unroll(0, n)], h)`: `n` cells, `⌊16n/136⌋ + 1`
blocks. -/
def keccakCells (n : Nat) : Source.Program :=
  hashMain [st (.call "keccak_cells" [plusOne 0 n, .var "h"])]

/-- The cells `j + 1` for `j` from `lo` below `hi`. -/
def counting (lo hi : Nat) : List E := (List.range' lo (hi - lo)).map fun j => litField (j + 1)

#guard [1, 8, 9, 17, 20, 34, 35].all fun n =>
  isOk (runMain (keccakCells n) (cellsDigest (counting 0 n) (16 * n)))
#guard !isOk (runMain (keccakCells 20) (cellsDigest (counting 0 19) (16 * 19)))

/-- `keccak_cells([const(j + 1) for j in unroll(0, 17)], s, final=0)`, then
`keccak_cells([const(j + 1) for j in unroll(17, 20)], h, state=s)`: the hash of the twenty
cells. -/
def keccakState : Source.Program :=
  hashMain [st (.let_ "s" (.stackBuf 13)),
    st (.call "keccak_cells" [plusOne 0 17,
      .var "s", kw "final" (.lit 0)]),
    st (.call "keccak_cells" [plusOne 17 20,
      .var "h", kw "state" (.var "s")])]

#guard isOk (runMain keccakState (cellsDigest (counting 0 20) 320))

/-- `keccak([1, 2], [3, 4], s)`, then the duplex step `keccak([5, 6], [7, 8], t, cap=s)`, its
first two cells published. -/
def keccakCap : Source.Program :=
  hashMain [st (.let_ "s" (.stackBuf 13)), st (.let_ "t" (.stackBuf 13)),
    st (.call "keccak" [.list [.lit 1, .lit 2], .list [.lit 3, .lit 4], .var "s"]),
    st (.call "keccak" [.list [.lit 5, .lit 6], .list [.lit 7, .lit 8], .var "t",
      kw "cap" (.var "s")]),
    st (.store (.var "h") (.lit 0) (.index (.var "t") (.lit 0))),
    st (.store (.var "h") (.lit 1) (.index (.var "t") (.lit 1)))]

open LeanVM.Semantics in
/-- Keccak-f[1600] of the thirteen cells, both layouts even. -/
def permCells (cells : List E) : List E :=
  (List.finRange 13).map (cellsOfState (keccakF1600 (stateOfCells (fun c => cells.getD c.val 0) false))
    false)

/-- The duplex step's output: the message `5, 6, 7, 8`, zero, then the first permutation's
cells `8` to `12`. -/
def capOut : List E :=
  let s := permCells (lits [1, 2, 3, 4] ++
    [keccakPadValue, 0, 0, 0, byteWord 135 0x80, 0, 0, 0, 0])
  permCells (lits [5, 6, 7, 8] ++ [0, 0, 0, 0] ++ s.drop 8)

#guard isOk (runMain keccakCap (capOut.take 2))
#guard !isOk (runMain keccakCap ((permCells (lits [5, 6, 7, 8] ++ List.replicate 9 0)).take 2))

/-- `g_power_of_word(v)`: `unroll`, bit hints, booleanity by a second write, and the product of
`1 + b·(1 + g^(2^j))`. -/
def gpowMain (v : Nat) : Source.Program :=
  withGuest ["g_power_of_word"]
    ([st (.let_ "r" (.call "g_power_of_word" [.lit v]))] ++ publish (.var "r") (.lit 0))

#guard (Expand.expandProgram (gpowMain 5)).toOption.map (·.map Core.Fn.name) ==
  some ["main", "g_power_of_word"]
#guard isOk (runMain (gpowMain 5) [gpowE 5, 0])
#guard isOk (runMain (gpowMain 63) [gpowE 63, 0])
#guard !isOk (runMain (gpowMain 5) [gpowE 6, 0])

/-! ## The whole guest against its bytecode

The guest expands to one core function per compiled function, in the compiler's order (after
`__jump_tables`), with the compiled function's name; and its `KECCAK` atoms are the compiled
function's `KECCAK` instructions, one for one and in order: the same layouts, as many written
cells as the instruction's `outCells`, and every value an atom reads or writes at one frame offset
of the instructions (`keccakIns`, `keccakOuts`) throughout
the function, each constant among them `SET` at its offset to its word. -/

mutual
/-- The atoms of a statement, every branch and arm. -/
def atomsOf : Core.Stmt → List Core.Atom
  | .atom a => [a]
  | .ite _ z n => atomsList z ++ atomsList n
  | .match_ _ arms => atomsArms arms
  | _ => []
def atomsList : List Core.Stmt → List Core.Atom
  | [] => []
  | s :: ss => atomsOf s ++ atomsList ss
def atomsArms : List (List Core.Stmt) → List Core.Atom
  | [] => []
  | a :: as => atomsList a ++ atomsArms as
end

/-- The `KECCAK` atoms of a core function: their read and written values and layouts. -/
def keccakAtoms (f : Core.Fn) : List (List Core.V × List Core.V × Bool × Bool) :=
  (atomsList f.body).filterMap fun
    | .keccak ins outs i o => some (ins, outs, i, o)
    | _ => none

/-- The `KECCAK` instructions of a compiled function: their read and written offsets and
layouts. -/
def keccakInstrs (c : CompiledFunction) : List (List Nat × List Nat × Bool × Bool) :=
  c.chunks.flatten.filterMap fun
    | .keccak m0 m1 m2 m3 tail b8 cap out i o oC =>
        some (keccakIns m0 m1 m2 m3 tail b8 cap, keccakOuts out oC.cellCount, i, o)
    | _ => none

/-- Whether a core function's `KECCAK` atoms are a compiled function's `KECCAK` instructions. -/
def keccakAgree (f : Core.Fn) (c : CompiledFunction) : Bool := Id.run do
  let as := keccakAtoms f
  let is := keccakInstrs c
  if as.length != is.length then return false
  let mut off : Std.HashMap Core.V Nat := {}
  for ((ins, outs, i, o), (ci, co, i', o')) in as.zip is do
    if i != i' || o != o' || ins.length != 13 || outs.length != co.length then return false
    for (v, k) in (ins ++ outs).zip (ci ++ co) do
      match off[v]? with
      | some k' => if k != k' then return false
      | none => off := off.insert v k
  let code := c.chunks.flatten
  return (atomsList f.body).all fun
    | .const v x => match off[v]? with
      | some k => code.any fun
          | .set k' c0 c1 => k' == k && limbsOf x == (c0, c1)
          | _ => false
      | none => true
    | _ => true

#guard match Expand.expandProgram Data.guest with
  | .ok fns => fns.length == 991 && fns.head?.map (·.name) == some "main" &&
      fns.getLast?.map (·.name) == some "walk_path__L18_L4" &&
      fns.map (·.name) == Data.functions.tail.map (·.name) &&
      (fns.zip Data.functions.tail).all fun (f, c) => keccakAgree f c
  | .error _ => false

end LeanVMTests.Guest.Expand
