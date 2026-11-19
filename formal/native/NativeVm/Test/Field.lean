import Native.Test.Run
import NativeVm.Field

/-!
# The field kernels against `K`, `E` and the verifier's functions

Each kernel runs on pseudo-random inputs and its result is compared with the compiled operation of
`Statement.Field` or function of `Statement.LeanVmVerifier`.
-/

namespace NativeVm.Test.FieldTest

open Native Native.Test LeanVM.Parameters LeanVM.Protocol.Verifier NativeVm.Field

/-- SplitMix64: the `n` words after `seed`. -/
def rnd (seed : UInt64) (n : Nat) : List UInt64 :=
  ((List.range n).foldl (fun (acc : List UInt64 × UInt64) _ ↦
    let x := acc.2 + 0x9e3779b97f4a7c15
    let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
    let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
    (acc.1 ++ [z ^^^ (z >>> 31)], x)) ([], seed)).1

/-- `n` pseudo-random elements of `E`. -/
def rndE (seed : UInt64) (n : Nat) : List E :=
  let ws := rnd seed (2 * n)
  (List.range n).map fun i ↦ eOf (ws.getD (2 * i) 0) (ws.getD (2 * i + 1) 0)

/-- The words of a list of `E` at `p`. -/
def eWordsAt (p : UInt64) (xs : List E) : List (UInt64 × UInt64) :=
  (List.range xs.length).flatMap fun i ↦
    let x := xs.getD i 0
    [(p + (16 * i).toUInt64, (x.limb 0).lane), (p + (16 * i).toUInt64 + 8, (x.limb 1).lane)]

/-- The list of `n` elements of `E` at `p`. -/
def readE (s : RState) (p : UInt64) (n : Nat) : List E :=
  (List.range n).map fun i ↦
    eOf (s.word (p + (16 * i).toUInt64)) (s.word (p + (16 * i).toUInt64 + 8))

def reg (s : RState) (r : Reg64) : UInt64 := s.regs.getD (regIdx r) 0

/-- Run `c` from the registers `rs` and the words `ws`; `none` if it gets stuck or fails. -/
def exec (c : Stmt) (rs : List (Reg64 × UInt64)) (ws : List (UInt64 × UInt64)) : Option RState :=
  let s := RState.ofWords 0x1000 ws
  let s := rs.foldl (fun s (r, v) ↦ { s with regs := s.regs.set! (regIdx r) v }) s
  match Native.Test.run 100000000 c s with
  | some (.ok s, _) => some s
  | _ => none

/-- `A`'s element after a run. -/
def resA (s : Option RState) : Option E := s.map fun s ↦ eOf (reg s .r9) (reg s .r10)

def eqE (a b : E) : Bool := (a.limb 0).lane == (b.limb 0).lane && (a.limb 1).lane == (b.limb 1).lane

def eqOE (a : Option E) (b : E) : Bool := match a with | some a => eqE a b | none => false

def eqL (a b : List E) : Bool := a.length == b.length && (a.zip b).all fun (x, y) ↦ eqE x y

def lanes (x : E) : List (Reg64 × UInt64) → List (Reg64 × UInt64) :=
  ([(.r9, (x.limb 0).lane), (.r10, (x.limb 1).lane)] ++ ·)

def lanesB (x : E) : List (Reg64 × UInt64) := [(.r11, (x.limb 0).lane), (.r12, (x.limb 1).lane)]

/-! ## `K` -/

def kAgree (seed : UInt64) : Bool :=
  let w := rnd seed 3
  let a := w.getD 0 0
  let b := w.getD 1 0
  let k := (w.getD 2 0 % 8).toNat
  (exec kmul [(.rax, a), (.rbx, b)] []).map (reg · .rax) == some (K.ofLane a * K.ofLane b).lane &&
  (exec ksq [(.rax, a)] []).map (reg · .rax) == some (K.ofLane a ^ 2).lane &&
  (exec ksqn [(.rax, a), (.rdx, k.toUInt64)] []).map (reg · .rax) ==
    some (K.ofLane a ^ 2 ^ k).lane &&
  (exec kinv [(.rax, a)] []).map (reg · .rax) == some (K.ofLane a)⁻¹.lane

#guard (rnd 1 20).all kAgree
#guard (exec kinv [(.rax, 0)] []).map (reg · .rax) == some 0
#guard (exec kinv [(.rax, 1)] []).map (reg · .rax) == some 1

/-! ## `E` -/

def eAgree (seed : UInt64) : Bool :=
  let xs := rndE seed 2
  let x := xs.getD 0 0
  let y := xs.getD 1 0
  let w := rnd (seed + 7) 2
  let k := (w.getD 0 0 % 6).toNat
  let n := w.getD 1 0 % 300
  eqOE (resA (exec eadd (lanes x (lanesB y)) [])) (x + y) &&
  eqOE (resA (exec emul (lanes x (lanesB y)) [])) (x * y) &&
  eqOE (resA (exec esq (lanes x []) [])) (x ^ 2) &&
  eqOE (resA (exec escale (lanes x [(.r11, (y.limb 0).lane)]) [])) (x * ofK (y.limb 0)) &&
  eqOE (resA (exec esqn (lanes x [(.rdx, k.toUInt64)]) [])) (x ^ 2 ^ k) &&
  eqOE (resA (exec epow (lanes x [(.r13, n)]) [])) (x ^ n.toNat)

#guard (rnd 2 20).all eAgree

/-! ## Lists -/

def xsP : UInt64 := 0x10000
def ysP : UInt64 := 0x20000
def workP : UInt64 := 0x30000

def listAgree (seed : UInt64) : Bool :=
  let n := ((rnd seed 1).getD 0 0 % 9).toNat
  let xs := rndE (seed + 1) n
  let ys := rndE (seed + 2) n
  let b := (rndE (seed + 3) 1).getD 0 0
  let ws := eWordsAt xsP xs ++ eWordsAt ysP ys
  let arr := [(.r13, xsP), (.r14, ysP), (.r15, n.toUInt64)]
  eqOE (resA (exec edot arr ws)) (dot xs ys) &&
  eqOE (resA (exec eeqEval arr ws)) (eqEval xs ys) &&
  eqOE (resA (exec epolyEval (lanesB b ++ [(.r13, xsP), (.r15, n.toUInt64)]) ws))
    (polyEval xs b) &&
  ((exec epowers (lanesB b ++ [(.r14, workP), (.r15, n.toUInt64)]) (eWordsAt workP ys)).map
    (readE · workP n)).any (eqL · (powers b n)) &&
  ((exec efold (lanesB b ++ [(.r13, xsP), (.r14, workP), (.r15, (n / 2).toUInt64)])
    (ws ++ eWordsAt workP ys)).map (readE · workP (n / 2))).any (eqL · (foldPairs b xs)) &&
  ((exec efold (lanesB b ++ [(.r13, xsP), (.r14, xsP), (.r15, (n / 2).toUInt64)]) ws).map
    (readE · xsP (n / 2))).any (eqL · (foldPairs b xs))

#guard (rnd 3 30).all listAgree

def mleAgree (seed : UInt64) : Bool :=
  let m := ((rnd seed 1).getD 0 0 % 6).toNat
  let mle := rndE (seed + 1) (2 ^ m)
  let point := rndE (seed + 2) m
  let ws := eWordsAt xsP mle ++ eWordsAt ysP point ++ eWordsAt workP mle
  eqOE (resA (exec emle [(.r13, xsP), (.r14, workP), (.rsi, ysP), (.r15, (2 ^ m : Nat).toUInt64)]
    ws)) (multilinearEval mle point) &&
  eqOE (resA (exec emle [(.r13, xsP), (.r14, xsP), (.rsi, ysP), (.r15, (2 ^ m : Nat).toUInt64)]
    ws)) (multilinearEval mle point)

#guard (rnd 4 20).all mleAgree

end NativeVm.Test.FieldTest
