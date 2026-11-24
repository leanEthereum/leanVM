import LeanVM.Cost.Compiler

/-!
# Tests: the compiler on small functions

`cost_compile` compiles a definition, a caller of it, and two recursive functions (on `ℕ` and on
lists); the specs are kernel-checked, with Lean's three axioms, and the assembled program computes
the functions' values.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost

def double (n : ℕ) : ℕ := n + n
cost_compile double at 1 := double

def quad (n : ℕ) : ℕ := double (double n)
cost_compile quad at 2 := quad

def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n
cost_compile sumTo at 3 measure fun n ↦ n := sumTo

def len : List ℕ → ℕ
  | [] => 0
  | _ :: xs => len xs + 1
cost_compile len at 4 measure fun l ↦ l.length := len

-- A library function with a function parameter, monomorphized at `ℕ`.
cost_compile foldlNat at 5 measure fun _ _ l ↦ l.length := @List.foldl ℕ ℕ

/-- A lambda capturing a variable, passed to `foldl`: lifted to a function of its own. -/
def sumScaled (d : ℕ) (l : List ℕ) : ℕ := l.foldl (fun acc x ↦ acc + x * d) 0
cost_compile sumScaled at 6 := sumScaled

/-- The program: the bodies at their indices. -/
def toyProgram : MachineProgram :=
  #[.literal (.nat 0), double.costBody, quad.costBody, sumTo.costBody, len.costBody,
    foldlNat.costBody, sumScaled.costBody, sumScaled.lam0.costBody]

#guard (evaluateFunctionBody toyProgram 10 2 [MachineEncoding.encodeValue (5 : ℕ)]).map (·.1) == some (MachineEncoding.encodeValue (quad 5))
#guard (evaluateFunctionBody toyProgram 20 3 [MachineEncoding.encodeValue (10 : ℕ)]).map (·.1) == some (MachineEncoding.encodeValue (sumTo 10))
#guard (evaluateFunctionBody toyProgram 20 4 [MachineEncoding.encodeValue [1, 2, 3]]).map (·.1) == some (MachineEncoding.encodeValue (3 : ℕ))

#guard (evaluateFunctionBody toyProgram 20 6 [MachineEncoding.encodeValue (3 : ℕ), MachineEncoding.encodeValue [1, 2, 3]]).map (·.1) ==
  some (MachineEncoding.encodeValue (18 : ℕ))
#check @sumScaled.costEq

-- The program holds the bodies the specs need.
example : Includes toyProgram [(3, sumTo.costBody)] := by
  intro p hp; simp at hp; subst hp; rfl

/-- info: 'LeanVMTests.Cost.sumTo.costSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sumTo.costSpec

/-! A recursive function compiled on demand at static arguments is named after them: a constant
by its last component, by its full name when another function has that name, and an error when
both are taken. -/

namespace ClashA
/-- A type former, a static argument of `lenAt`. -/
def Box (α : Type) : Type := α
end ClashA

namespace ClashB
/-- A type former with the same last component as `ClashA.Box`. -/
def Box (α : Type) : Type := α × α
end ClashB

namespace ClashC
/-- A third `Box`. -/
def Box (α : Type) : Type := Option α
end ClashC

/-- A list's length, at a type former it ignores. -/
def lenAt (M : Type → Type) : List ℕ → ℕ
  | [] => 0
  | _ :: xs => lenAt M xs + 1

/-- `lenAt` at `ClashA.Box`. -/
def lenA (l : List ℕ) : ℕ := lenAt ClashA.Box l
cost_compile lenA := lenA

/-- `lenAt` at `ClashB.Box`. -/
def lenB (l : List ℕ) : ℕ := lenAt ClashB.Box l
cost_compile lenB := lenB

example := @LeanVM.Cost.Auto.LeanVMTests.Cost.lenAt.Box.costEq
example := @LeanVM.Cost.Auto.LeanVMTests.Cost.lenAt.«LeanVMTests.Cost.ClashB.Box».costEq

/-- The full name taken too. -/
set_option linter.dupNamespace false in
def _root_.LeanVM.Cost.Auto.LeanVMTests.Cost.lenAt.«LeanVMTests.Cost.ClashC.Box».costIdx : ℕ := 0

/-- `lenAt` at `ClashC.Box`. -/
def lenC (l : List ℕ) : ℕ := lenAt ClashC.Box l

/--
error: compile LeanVMTests.Cost.lenAt: LeanVM.Cost.Auto.LeanVMTests.Cost.lenAt.«LeanVMTests.Cost.ClashC.Box» is compiled already at other static arguments; compile this call with `cost_compile` under a name of its own
-/
#guard_msgs in
cost_compile lenC := lenC

end LeanVMTests.Cost
