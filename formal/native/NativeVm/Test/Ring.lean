import Native.Test.Run
import NativeVm.Code.Phase7.RingRuns

/-!
# Ring switching's arithmetic and weight kernels against the model

`ringPure` runs on pseudo-random challenges and slices laid out as phase 7a leaves them, and its
target and coefficients (`RingAt`'s words) are compared with `Model.ringTarget` and
`Model.ringCoefficients`; `weightRing` and `weightEq` with `StackWeight.eval`.
-/

namespace NativeVm.Test.RingTest

open Native Native.Test NativeVm.Model NativeVm.Code.Ring

def rnd (seed : UInt64) (n : Nat) : List UInt64 :=
  ((List.range n).foldl (fun (acc : List UInt64 × UInt64) _ ↦
    let x := acc.2 + 0x9e3779b97f4a7c15
    let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
    let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
    (acc.1 ++ [z ^^^ (z >>> 31)], x)) ([], seed)).1

def rndW (seed : UInt64) (n : Nat) : Array EW :=
  let ws := rnd seed (2 * n)
  ((List.range n).map fun i ↦ (⟨ws.getD (2 * i) 0, ws.getD (2 * i + 1) 0⟩ : EW)).toArray

def W : UInt64 := 0x100000

def wordsAt (k : Nat) (xs : Array EW) : List (UInt64 × UInt64) :=
  (List.range xs.size).flatMap fun i ↦
    let x := xs.getD i 0
    [(W + (8 * (k + 2 * i)).toUInt64, x.c0), (W + (8 * (k + 2 * i + 1)).toUInt64, x.c1)]

def readW (s : RState) (k n : Nat) : Array EW :=
  ((List.range n).map fun i ↦
    (⟨s.word (W + (8 * (k + 2 * i)).toUInt64), s.word (W + (8 * (k + 2 * i + 1)).toUInt64)⟩ : EW)).toArray

def zeros (k n : Nat) : List (UInt64 × UInt64) :=
  (List.range n).map fun j ↦ (W + (8 * (k + j)).toUInt64, 0)

def setRegs (s : RState) (rs : List (Reg64 × UInt64)) : RState :=
  rs.foldl (fun s (r, v) ↦ { s with regs := s.regs.set! (regIdx r) v }) s

def pureOk (seed : UInt64) : Bool :=
  let ch := rndW seed 16
  let sl := rndW (seed + 1) 64
  let f := ch.extract 0 8
  let g := ch.extract 8 16
  let s := setRegs (RState.ofWords 0 (wordsAt chO ch ++ wordsAt slO sl ++ zeros tgO 130 ++
    zeros imgO 130)) [(.rbp, W)]
  match run 100000000 ringPure s with
  | some (.ok s', _) =>
    readW s' tgO 1 == #[ringTarget sl f g] && readW s' cfO 64 == ringCoefficients f g
  | _ => false

def weightRingOk (seed : UInt64) (vc idx : Nat) : Bool :=
  let r := rndW seed 36
  let c := rndW (seed + 1) 64
  let x := rndW (seed + 2) 20
  let rO := 1000
  let cO := 2000
  let xO := 3000
  let bO := 4000
  let s := RState.ofWords 0 (wordsAt rO r ++ wordsAt cO c ++ wordsAt xO x ++ zeros bO bufWords)
  let s := setRegs s [(.r13, W + (8 * rO).toUInt64), (.r15, 36), (.r14, W + (8 * xO).toUInt64),
    (.rbp, 20), (.r11, W + (8 * cO).toUInt64), (.r12, 64), (.rsi, idx.toUInt64),
    (.rdx, vc.toUInt64), (.rbx, W + (8 * bO).toUInt64)]
  match run 100000000 weightRing s with
  | some (.ok s', _) =>
    (⟨s'.regs.getD 9 0, s'.regs.getD 10 0⟩ : EW) == StackWeight.eval (.ring ⟨vc, idx⟩ r c) x
  | _ => false

def weightEqOk (seed : UInt64) (vc idx sl : Nat) : Bool :=
  let pt := rndW seed 12
  let x := rndW (seed + 2) 20
  let s := RState.ofWords 0 (wordsAt 1000 pt ++ wordsAt 3000 x)
  let s := setRegs s [(.r13, W + 8000), (.r15, 12), (.r14, W + 24000), (.rbp, 20),
    (.rsi, idx.toUInt64), (.rdx, vc.toUInt64), (.rcx, sl.toUInt64)]
  match run 100000000 weightEq s with
  | some (.ok s', _) =>
    (⟨s'.regs.getD 9 0, s'.regs.getD 10 0⟩ : EW) ==
      StackWeight.eval (.eq (stackPoint ⟨vc, idx⟩ pt sl)) x
  | _ => false

/-- Every check, for a compiled runner (the interpreter is too slow for `ringPure`). -/
def all : List Bool :=
  [pureOk 1, pureOk 7, weightRingOk 3 12 0x5a5, weightRingOk 4 36 7, weightRingOk 5 25 0x1f3,
    weightEqOk 3 12 0x5a5 20, weightEqOk 4 8 0x3 25, weightEqOk 5 12 1 12]

end NativeVm.Test.RingTest
