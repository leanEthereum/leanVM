import LeanVM.Cost.Encoding

/-!
# Tests: the cost machine

* each primitive on sample values, with its price;
* misuse fails: a primitive on the wrong kind of value, a variable or a field that does not exist,
  a call of a missing function, too little fuel;
* Keccak-f[1600] written in the language (one function per round, a recursive loop over the 24
  round constants) equals the statement's `keccakF1600`, at `26648 ≈ 2^14.7` per permutation.
-/

namespace LeanVMTests.Cost

open LeanVM.Cost LeanVM.Semantics LeanVM.Parameters

/-! ## Primitives -/

-- Natural numbers: priced by 64-bit limbs, the larger count read or written (`1` on words).
#guard PrimitiveOperation.bitwiseAnd.apply [.nat 12, .nat 10] == some (.nat 8, 1)
#guard PrimitiveOperation.bitwiseOr.apply [.nat 12, .nat 10] == some (.nat 14, 1)
#guard PrimitiveOperation.bitwiseXor.apply [.nat 12, .nat 10] == some (.nat 6, 1)
#guard PrimitiveOperation.bitwiseXor.apply [.nat 0, .nat (2 ^ 64 - 1)] == some (.nat (2 ^ 64 - 1), 1)
#guard PrimitiveOperation.shiftLeft.apply [.nat 1, .nat 65] == some (.nat (2 ^ 65), 2)
#guard PrimitiveOperation.shiftRight.apply [.nat 8, .nat 3] == some (.nat 1, 1)
#guard PrimitiveOperation.equal.apply [.nat 8, .nat 8] == some (.ofBool true, 1)
#guard PrimitiveOperation.lessThan.apply [.nat 9, .nat 8] == some (.ofBool false, 1)
#guard PrimitiveOperation.add.apply [.nat (2 ^ 64), .nat 1] == some (.nat (2 ^ 64 + 1), 2)
#guard PrimitiveOperation.add.apply [.nat (2 ^ 64 - 1), .nat 1] == some (.nat (2 ^ 64), 2)
#guard PrimitiveOperation.truncatedSubtract.apply [.nat 3, .nat 5] == some (.nat 0, 1)
#guard PrimitiveOperation.multiply.apply [.nat (2 ^ 64), .nat (2 ^ 128)] == some (.nat (2 ^ 192), 6)
#guard PrimitiveOperation.multiply.apply [.nat (2 ^ 63), .nat 2] == some (.nat (2 ^ 64), 2)
#guard PrimitiveOperation.divide.apply [.nat 17, .nat 5] == some (.nat 3, 1)
#guard PrimitiveOperation.modulo.apply [.nat 17, .nat 5] == some (.nat 2, 1)
#guard PrimitiveOperation.equal.apply [.nat 5, .nat 5] == some (.ofBool true, 1)
#guard PrimitiveOperation.lessThan.apply [.nat 5, .nat 5] == some (.ofBool false, 1)
#guard PrimitiveOperation.shiftLeft.apply [.nat 1, .nat 128] == some (.nat (2 ^ 128), 3)
#guard PrimitiveOperation.shiftRight.apply [.nat (2 ^ 128), .nat 127] == some (.nat 2, 3)
-- The carry-less product: `(x + 1)·(x + 1) = x^2 + 1`; two limbs written at `2`.
#guard PrimitiveOperation.carrylessMultiply.apply [.nat 3, .nat 3] == some (.nat 5, 1)
#guard PrimitiveOperation.carrylessMultiply.apply [.nat (2 ^ 63), .nat 2] == some (.nat (2 ^ 64), 2)
-- Arrays: a new array of `n` entries costs `n + 1`.
#guard PrimitiveOperation.arraySize.apply [.array #[.nat 1, .nat 2]] == some (.nat 2, 1)
#guard PrimitiveOperation.arrayGet.apply [.array #[.nat 1, .nat 2], .nat 1, .nat 0] == some (.nat 2, 1)
#guard PrimitiveOperation.arrayGet.apply [.array #[.nat 1, .nat 2], .nat 5, .nat 0] == some (.nat 0, 1)
#guard PrimitiveOperation.arraySet.apply [.array #[.nat 1, .nat 2], .nat 0, .nat 7] == some (.array #[.nat 7, .nat 2], 3)
#guard PrimitiveOperation.arrayPush.apply [.array #[.nat 1], .nat 7] == some (.array #[.nat 1, .nat 7], 3)
#guard PrimitiveOperation.arrayOfList.apply [.ofList [.nat 1, .nat 2]] == some (.array #[.nat 1, .nat 2], 3)
#guard PrimitiveOperation.arrayToList.apply [.array #[.nat 1, .nat 2]] == some (.ofList [.nat 1, .nat 2], 7)
#guard PrimitiveOperation.arrayAppend.apply [.array #[.nat 1], .array #[.nat 2]] == some (.array #[.nat 1, .nat 2], 3)
#guard PrimitiveOperation.arrayExtract.apply [.array #[.nat 1, .nat 2, .nat 3], .nat 1, .nat 9] ==
  some (.array #[.nat 2, .nat 3], 3)
#guard PrimitiveOperation.arrayReplicate.apply [.nat 2, .nat 0] == some (.array #[.nat 0,
    .nat 0], 3)

/-! ## Misuse fails -/

#guard PrimitiveOperation.bitwiseAnd.apply [.constructor 0 [], .nat 2] == none
#guard PrimitiveOperation.bitwiseAnd.apply [.nat 1] == none
#guard PrimitiveOperation.arrayGet.apply [.nat 1, .nat 0, .nat 0] == none
#guard PrimitiveOperation.arrayOfList.apply [.constructor 1 [.nat 1, .nat 2]] == none
#guard evaluateTerm #[] 5 [] (.position 0) == none
#guard evaluateTerm #[] 5 [] (.field 2 (.constructor 0 [.literal (.nat 1)])) == none
#guard evaluateTerm #[] 5 [] (.case (.literal (.nat 1)) [.literal (.nat 2)]) == none
#guard evaluateTerm #[] 5 [] (.case (.constructor 3 []) [.literal (.nat 2)]) == none
#guard evaluateTerm #[] 5 [] (.call 0 []) == none
#guard evaluateTerm #[] 5 [] (.applyClosure (.literal (.nat 0)) []) == none
-- A function that calls itself forever runs out of fuel.
#guard runMachineProgram #[.call 0 [.position 0]] 1000 (.nat 0) == none
-- Prices: a variable `1`, a constructor of `n` values `n + 1`, a field `1`, a `let` `1`.
#guard runMachineProgram #[.letIn (.constructor 4 [.position 0, .position 0]) (.field 1 (.position
    0))] 1 (.nat 9) == some (.nat 9, 8)
-- A `case` costs `1` and the fields it puts in front of the environment; a closure's application
-- `1` and its captured values.
#guard runMachineProgram #[.case (.constructor 4 [.position 0, .position 0]) [.position 9, .position 9, .position 9, .position 9, .position 1]] 1 (.nat 9) ==
  some (.nat 9, 9)
#guard runMachineProgram #[.applyClosure (.closure 1 [.position 0, .position 0]) [.position 0], .position 2] 1 (.nat 9) == some (.nat 9, 10)
-- The output within a budget and a size bound (the program's size is `6`).
#guard outputWithin #[.letIn (.constructor 4 [.position 0, .position 0]) (.field 1 (.position 0))] 6
    8 (.nat 9) ==
  some (.nat 9)
#guard outputWithin #[.letIn (.constructor 4 [.position 0, .position 0]) (.field 1 (.position 0))] 6
    7 (.nat 9) == none
#guard outputWithin #[.letIn (.constructor 4 [.position 0, .position 0]) (.field 1 (.position 0))] 5
    8 (.nat 9) == none

/-! ## Keccak-f[1600] in the language -/

/-- A term at an environment of a given length: variables named by the length at which they were
bound, turned into positions. -/
abbrev B := ℕ → Term

/-- Argument `j` of `n`. -/
def arg (n j : ℕ) : B := fun d ↦ .position (d - n + j)

/-- `let x := t; body x`. -/
def letB (t : B) (body : B → B) : B := fun d ↦ .letIn (t d) (body (fun d' ↦ .position (d' - d - 1)) (d + 1))

/-- `let`s of a list of terms, in order. -/
def letsB : List B → (List B → B) → B
  | [], k => k []
  | t :: ts, k => letB t fun x ↦ letsB ts fun xs ↦ k (x :: xs)

def opB (o : PrimitiveOperation) (args : List B) : B := fun d ↦ .primitive o (args.map (· d))

def wlit (x : UInt64) : B := fun _ ↦ .literal (.nat x.toNat)

def nlit (n : ℕ) : B := fun _ ↦ .literal (.nat n)

def xorB (a b : B) : B := opB .bitwiseXor [a, b]

/-- `rot(x, n)` on a word: `((x &&& (2^(64-n) - 1)) <<< n) ||| (x >>> (64 - n))`. -/
def rotB (x : B) (n : ℕ) : B :=
  if n = 0 then x else opB .bitwiseOr [opB .shiftLeft [opB .bitwiseAnd [x, nlit (2 ^ (64 - n) - 1)], nlit n],
    opB .shiftRight [x, nlit (64 - n)]]

/-- A list value of the terms. -/
def listB : List B → B
  | [] => fun _ ↦ .constructor 0 []
  | t :: ts => fun d ↦ .constructor 1 [t d, listB ts d]

/-- One round on the state (argument `0`) with the round constant (argument `1`). -/
def roundB : B :=
  letsB ((List.range 25).map fun i ↦ opB .arrayGet [arg 2 0, nlit i, wlit 0]) fun a ↦
  letsB ((List.range 5).map fun x ↦
      xorB (a[x]!) (xorB (a[x + 5]!) (xorB (a[x + 10]!) (xorB (a[x + 15]!) (a[x + 20]!))))) fun c ↦
  letsB ((List.range 25).map fun i ↦
      xorB (a[i]!) (xorB (c[(i + 4) % 5]!) (rotB (c[(i + 1) % 5]!) 1))) fun a ↦
  let src := fun j ↦ ((List.range 25).find? fun i ↦ keccakPi i = j).getD 0
  letsB ((List.range 25).map fun j ↦ rotB (a[src j]!) (keccakRho.getD (src j) 0)) fun b ↦
  letsB ((List.range 25).map fun i ↦
      xorB (b[i]!) (opB .bitwiseAnd [xorB (b[i - i % 5 + (i + 1) % 5]!) (nlit (2 ^ 64 - 1)),
        b[i - i % 5 + (i + 2) % 5]!])) fun a ↦
  opB .arrayOfList [listB ((a.set 0 (xorB (a[0]!) (arg 2 1))))]

/-- The program: `0` runs the rounds from round `0`; `1` the rounds from round `i` (argument `1`);
`2` one round. -/
def keccakProgram : LeanVM.Cost.MachineProgram := #[
  .call 1 [.position 0, .literal (.nat 0)],
  .case (.primitive .lessThan [.position 1, .literal (.nat 24)]) [
    .position 0,
    .call 1 [.call 2 [.position 0, .primitive .arrayGet [.literal (.array (keccakRC.toArray.map (.nat ·.toNat))), .position 1,
      .literal (.nat 0)]], .primitive .add [.position 1, .literal (.nat 1)]]],
  roundB 2]

def stateA : KeccakState := Vector.ofFn fun i ↦ (i.val * 0x9E3779B97F4A7C15 + 7).toUInt64

#guard (runMachineProgram keccakProgram 100 (MachineEncoding.encodeValue (0 : KeccakState))).map
    (·.1) ==
  some (MachineEncoding.encodeValue (keccakF1600 0))
#guard (runMachineProgram keccakProgram 100 (MachineEncoding.encodeValue stateA)).map (·.1) == some (MachineEncoding.encodeValue (keccakF1600 stateA))
-- The price of one permutation: `26648`, between `2^14` and `2^15`.
#guard (runMachineProgram keccakProgram 100 (MachineEncoding.encodeValue stateA)).map
    (·.2) == some 26648

end LeanVMTests.Cost
