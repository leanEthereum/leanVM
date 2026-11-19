import NativeVm.Test.Transcript
import NativeVm.Code.Phase3.GkrCode
import NativeVm.Code.Contracts

/-!
# The GKR walk's code against the model

An honest stream for `Model.verifyGkrGrandProducts depth` is built step by step (each step's last
child chosen so that the products match the claim), then `P3.gkrCode` runs from a state holding the
model's transcript state and `depth` at `depthR`: it must return the model's count root, point and
values, and agree on the sponge and the cursor; with a scalar changed, both must reject.
-/

namespace NativeVm.Test.Phase3GkrTest

open Native Native.Test NativeVm NativeVm.Transcript NativeVm.Model NativeVm.Code NativeVm.Code.P3
open NativeVm.Test.TranscriptTest
open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile

/-- A pseudo-random element. -/
def rnd (n : Nat) : EW :=
  ⟨(n * 0x9e3779b97f4a7c15 + 0x0123456789abcdef).toUInt64, (n * 0xc2b2ae3d27d4eb4f + 77).toUInt64⟩

/-- `a^(2^128 - 2)`, the inverse in `E`. -/
def einv (a : EW) : EW := Id.run do
  let mut acc : EW := 1
  let mut b := a
  for i in [0:128] do
    if i ≠ 0 then acc := acc * b
    b := b * b
  return acc

/-- The model's transcript state with the stream `stream`. -/
def tstate (stream : Array EW) : TState :=
  ⟨⟨Vector.replicate 25 7, #[], none⟩, stream, 0, #[], 0, #[]⟩

/-- An honest stream of `depth` layers. -/
def honest (depth : Nat) : Option (Array EW) := do
  let mut stream : Array EW := #[rnd 1, rnd 2]
  let ((shared, count), t) ← (do
    let a ← readScalar; let b ← readScalar; pure (a, b) : VM (EW × EW)).run (tstate stream)
  let mut t := t
  let mut st : GkrStateW := ⟨#[shared, shared, count], #[]⟩
  let mut rem := depth
  let mut seed := 10
  for _ in [0:depth] do
    if rem = 0 then break
    let step := gkrStepOf rem
    let n := 2 ^ step
    let pos := stream.size
    let total := n * st.point.size + 3 * n
    for i in [0:total] do stream := stream.push (rnd (seed + i))
    seed := seed + total
    for i in [0:n] do stream := stream.set! (pos + total - n + i) 1
    let t1 := { t with stream := stream }
    let ((claim, comb, c0, c1), _) ← (do
      let comb ← sampleChallenge
      let r ← sumcheck (polyEval st.values comb) (n + 1) (st.point.map some)
      let c0 ← readScalars n
      let c1 ← readScalars n
      pure (r.2, comb, c0, c1) : VM _).run t1
    let p2 := (claim + prodE c0 + prodE c1 * comb) * einv (comb * comb)
    stream := stream.set! (pos + total - n) p2
    let (st', t') ← (gkrStep step (rem = step) st).run { t with stream := stream }
    st := st'
    t := t'
    rem := rem - step
  return stream

/-- The sponge's context words. -/
def spongeWords (sp : SpongeW) : List (Nat × UInt64) :=
  let lane := fun i ↦ match sp.pending[i / 4]? with
    | some (x, tag) => if i % 4 = 0 then x.c0 else if i % 4 = 1 then x.c1 else if i % 4 = 2 then 0 else tag
    | none => 0
  (List.range 25).map (fun i ↦ (laneW + i, sp.state[i]!)) ++
    (List.range 16).map (fun i ↦ (rateW + i, lane i)) ++ [(countW, sp.pending.size.toUInt64)] ++
    match sp.ground with
    | none => [(groundW, 0)]
    | some c => [(groundW, 1), (groundW + 1, c.c0), (groundW + 2, c.c1)]

/-- The machine state before the walk. -/
def startState (depth : Nat) (stream : Array EW) : RState :=
  let t := tstate stream
  let π : Proof := ⟨stream.toList.map EW.toE, []⟩
  let L := 16 * stream.size + 5
  let ctxWords : List (Nat × UInt64) := (List.range ctxEnd).map fun k ↦
    (k, if k = ctxDecoded then decA else if k = ctxWork then workA else 0)
  RState.ofWords ctxA <|
    (ctxWords ++ spongeWords t.sponge).map (fun (k, v) ↦ (wd ctxA k, v)) ++
    (decodedImage L π).map (fun (k, v) ↦ (wd decA k, v)) ++
    (List.range dataEnd).map (fun k ↦ (wd workA k, 0)) ++
    [(wd workA workCursor, 0), (wd workA workPhase, 0), (wd workA workPhasePtr, wd decA (phaseBase L 0)),
      (wd workA workPhaseCount, 0), (wd workA workRootCount, 0), (wd workA depthR.off, depth.toUInt64)]

def readArr (s : RState) (k n : Nat) : Array EW :=
  (Array.range n).map fun i ↦ ⟨s.word (wd workA (k + 2 * i)), s.word (wd workA (k + 2 * i + 1))⟩

def spongeAgrees (s : RState) (sp : SpongeW) : Bool :=
  (spongeWords sp).all fun (k, v) ↦ s.word (wd ctxA k) == v

/-- `some true`: both accept, agreeing; `some false`: both reject; `none`: disagreement. -/
def check (depth : Nat) (stream : Array EW) : Option Bool := do
  let r ← Native.Test.run 1000000000 gkrCode (startState depth stream)
  match (verifyGkrGrandProducts depth).run (tstate stream), r with
  | none, (.err _, _) => some false
  | some ((count, point, values), t'), (.ok s', _) =>
    let ok := readArr s' countR.off 1 == #[count] && readArr s' pointR.off depth == point &&
      readArr s' treeR.off 3 == values && spongeAgrees s' t'.sponge &&
      s'.word (wd workA workCursor) == t'.cursor.toUInt64 && point.size == depth
    if ok then some true else none
  | _, _ => none

def runAll : IO Unit := do
  for depth in [0, 1, 2, 3, 4, 5, 7] do
    let some stream := honest depth | throw (IO.userError s!"depth {depth}: no honest stream")
    unless check depth stream == some true do throw (IO.userError s!"depth {depth}: honest run")
    for k in [2, stream.size / 2, stream.size - 1] do
      if 0 < depth && k < stream.size then
        let stream' := stream.modify k fun x ↦ { x with c0 := x.c0 ^^^ 1 }
        unless check depth stream' == some false do
          throw (IO.userError s!"depth {depth}: scalar {k} changed")
    IO.println s!"depth {depth}: agree ({stream.size} scalars)"

end NativeVm.Test.Phase3GkrTest
