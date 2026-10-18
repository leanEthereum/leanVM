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

def wordOf (c : Nat × Nat × Nat) : E := word c.1 c.2.1 c.2.2

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
  %s1#2 = (13503953895743350343, 11912009169889063794, 0)
  %s1#2[1] = (11170449402626986623, 6620516960021240235, 0)
  %s1#3 = (64, 4294967295, 0)
  %s0#0, %s0#0[1] = blake2s([%s1#0, %s1#0[1], %s1#1, %s1#1[1]], cv [%s1#2, %s1#2[1]], md %s1#3)
  %s2#0 = %s0#0
  %s2#0[1] = %s0#0[1]
  return %s2#0, %s2#0[1]
def hash_pair__L1(%#0):
  %s1#0 = mem[%#0 g^2]
  %s1#0[1] = mem[%#0 g^3]
  %s1#1 = mem[%#0 g^2]
  %s1#1[1] = mem[%#0 g^3]
  %s1#2 = (13503953895743350343, 11912009169889063794, 0)
  %s1#2[1] = (11170449402626986623, 6620516960021240235, 0)
  %s1#3 = (64, 4294967295, 0)
  %s0#0, %s0#0[1] = blake2s([%s1#0, %s1#0[1], %s1#1, %s1#1[1]], cv [%s1#2, %s1#2[1]], md %s1#3)
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

/-- `fs_compress([7, 9], 11, 1, out)`, the digest published. -/
def fsMain : Source.Program :=
  withGuest ["fs_compress"] ([st (.let_ "s" (.list [.lit 7, .lit 9])), st (.let_ "out" (.stackBuf 2)),
    st (.call "fs_compress" [.var "s", .lit 11, .lit 1, .var "out"])] ++
    publish (.index (.var "out") (.lit 0)) (.index (.var "out") (.lit 1)))

/-- info: def main():
  %s0#0 = 7
  %s0#0[1] = 9
  %s2#0 = 11
  hint [%s2.i1:fs_compress.s0#0, %s2.i1:fs_compress.s0#0[1], %s2.i1:fs_compress.s0#0[2]] = limbs %s2#0
  %s2.i1:fs_compress.s2#0 = 1
  assert_in_k %s2.i1:fs_compress.s0#0[2], %s2.i1:fs_compress.s2#0
  %s2.i1:fs_compress.s4#0 = (0, 0, 1)
  %s2.i1:fs_compress.s4#1 = %s2.i1:fs_compress.s4#0 * %s2.i1:fs_compress.s0#0[2]
  %s2.i1:fs_compress.s3#0 = %s2#0 + %s2.i1:fs_compress.s4#1
  %s2.i1:fs_compress.s5#0 = (0, 1, 0)
  %s2.i1:fs_compress.s3#0[1] = %s2.i1:fs_compress.s0#0[2] + %s2.i1:fs_compress.s5#0
  %s2.i1:fs_compress.s6#0 = (13503953895743350343, 11912009169889063794, 0)
  %s2.i1:fs_compress.s6#0[1] = (11170449402626986623, 6620516960021240235, 0)
  %s2.i1:fs_compress.s6#1 = (64, 4294967295, 0)
  %s1#0, %s1#0[1] = blake2s([%s0#0, %s0#0[1], %s2.i1:fs_compress.s3#0, %s2.i1:fs_compress.s3#0[1]], cv [%s2.i1:fs_compress.s6#0, %s2.i1:fs_compress.s6#0[1]], md %s2.i1:fs_compress.s6#1)
  %s4#0 = 1
  %s1#0 = mem[%s4#0 g^0]
  %s5#0 = 1
  %s5#1 = 2
  %s5#2 = %s5#0 * %s5#1
  %s1#0[1] = mem[%s5#2 g^0]
  return -/
#guard_msgs in
#eval IO.println (showProgram fsMain)

/-- The Spec's compression of the block `fs_compress` builds: the state, then `11` and `y`. -/
def fsDigest : List E :=
  let h := LeanVM.Semantics.compress
    (LeanVM.Semantics.cellWords ivCells.1 ++ LeanVM.Semantics.cellWords ivCells.2)
    (LeanVM.Semantics.messageWords ![word 7 0 0, word 9 0 0, word 11 0 0, word 0 1 0]) 64
    0xFFFFFFFF 0
  [LeanVM.Semantics.wordsCell #v[h[0], h[1], h[2], h[3]],
   LeanVM.Semantics.wordsCell #v[h[4], h[5], h[6], h[7]]]

#guard isOk (runMain fsMain fsDigest)
#guard !isOk (runMain fsMain [fsDigest[0]!, fsDigest[1]! + 1])

/-- `g_power_of_word(5, g_squares, 6)` over `exponent_tables()`: `Const` specialization, `unroll`,
a heap table, bit hints and a tuple return. -/
def gpowMain (v : Nat) : Source.Program :=
  withGuest ["exponent_tables", "g_power_of_word"]
    ([st (.letTuple ["logs", "sq"] "exponent_tables" []),
      st (.let_ "r" (.call "g_power_of_word" [.lit v, .var "sq", .lit 6]))] ++
      publish (.var "r") (.lit 0))

#guard (Expand.expandProgram (gpowMain 5)).toOption.map (·.map Core.Fn.name) ==
  some ["main", "exponent_tables", "g_power_of_word__L6"]
#guard isOk (runMain (gpowMain 5) [gpowE 5, 0])
#guard isOk (runMain (gpowMain 63) [gpowE 63, 0])
#guard !isOk (runMain (gpowMain 5) [gpowE 6, 0])

/-! ## `walk_group`, a dispatch arm

`verify_lean_xmss` dispatches each group of three base-4 digits to an inlined `walk_group` arm:
arm `k` walks chain `r` from its digit `(k / 4^r) % 4` to the top, one BLAKE2s per step. -/

mutual
def nBlake : Core.Stmt → Nat
  | .atom (.blake2s ..) => 1
  | .atom _ => 0
  | .ite _ z n => nBlakeList z + nBlakeList n
  | .match_ _ arms => nBlakeArms arms
  | _ => 0
def nBlakeList : List Core.Stmt → Nat
  | [] => 0
  | s :: ss => nBlake s + nBlakeList ss
def nBlakeArms : List (List Core.Stmt) → Nat
  | [] => 0
  | a :: as => nBlakeList a + nBlakeArms as
end

/-- The arms of the `match` statements of a block, in order. -/
def matchArms : List Core.Stmt → List (List (List Core.Stmt)) :=
  List.filterMap fun
    | .match_ _ arms => some arms
    | _ => none

def xmss : Option Core.Fn :=
  (Expand.expandFn Data.guest (guestFn "verify_lean_xmss")).toOption.map (·.1)

-- Two layers of 19 three-digit groups and one last digit.
#guard (xmss.map fun f => (matchArms f.body).map List.length) ==
  some (List.replicate 19 64 ++ [4] ++ List.replicate 19 64 ++ [4])
#guard xmss.any fun f => (matchArms f.body).all fun arms =>
  (List.range arms.length).all fun k =>
    nBlakeList arms[k]! == ((List.range (if arms.length == 64 then 3 else 1)).map fun r =>
      3 - (k / 4 ^ r) % 4).sum

/-! ## The whole guest -/

-- The guest expands, function for function in the compiler's order (`DBG_DISASM` lists the same
-- 1043 names after `__jump_tables`).
#guard match Expand.expandProgram Data.guest with
  | .ok fns => fns.length == 1043 && fns.head?.map (·.name) == some "main" &&
      fns.getLast?.map (·.name) == some "__loop487"
  | .error _ => false

end LeanVMTests.Guest.Expand
