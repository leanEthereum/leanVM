import Native.Test.Run
import NativeVm.Transcript.Code


/-!
# The transcript's gadgets against `run`

Programs of the verifier language built from the transcript's operations (`Op`) run on a proof two
ways: the statement's `run` over Keccak-f[1600] from `spongeSeedWith`, and the gadgets in sequence
(`seed`, one gadget per operation, `finish`) on the decoded proof's words. Each reports what the
operations return (a scalar's or a challenge's two limbs, a query's rows' words) and whether the
proof was consumed, or that it rejected; the two must agree. A synthetic proof (a stream and a
Merkle tree of height two) is always run; the verifier fixtures (`scripts/export-verifier-fixtures-
rust.sh`, from `$LEANVM_FIXTURES`, default `/tmp/vmfix`) when present.
-/

namespace NativeVm.Test.TranscriptTest

open Native Native.Test NativeVm NativeVm.Transcript
open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier

/-! ## The programs -/

/-- An operation of the transcript. -/
inductive Op
  | read
  | sample
  | grind (bits : Nat)
  | commit (height width : Nat)
  | query (i : Nat) (positions : List Nat)

/-- An operation as a program, returning its words. -/
def Op.prog : Op → VerifierProgram (List UInt64)
  | .read => do return eWords (← VerifierProgram.readScalar)
  | .sample => do return eWords (← VerifierProgram.sampleChallenge)
  | .grind bits => .grind bits (.ret [])
  | .commit h w => do VerifierProgram.readCommitment h w; return []
  | .query i ps => do return (← VerifierProgram.queryOpenings i ps).flatMap (·.map K.lane)

/-- The operations in order. -/
def progOf : List Op → VerifierProgram (List (List UInt64))
  | [] => pure []
  | o :: os => do
    let a ← o.prog
    let r ← progOf os
    return a :: r

/-- The statement's answer: the operations' words and whether the proof is consumed. -/
def specRun (bytecode : List K) (pub : Digest) (π : Proof) (ops : List Op) :
    Option (List (List UInt64) × Bool) :=
  let seed := Id.run (spongeSeedWith (m := Id) keccakF1600 bytecode pub)
  (Id.run (run (m := Id) keccakF1600 (progOf ops) ⟨⟨seed, [], none⟩, π.stream, π.openings, []⟩)).map
    fun (outs, st) ↦ (outs, st.stream.isEmpty && st.openings.isEmpty)

/-! ## The memory -/

def ctxA : UInt64 := 0x10000
def decA : UInt64 := 0x1000000
def workA : UInt64 := 0x40000000
def posA : UInt64 := 0x50000000
def outA : UInt64 := 0x60000000
def bcA : UInt64 := 0x70000000

/-- The decoded proof's words, as `Decoded` lays them out. -/
def decodedImage (L : Nat) (π : Proof) : List (Nat × UInt64) :=
  [(0, π.stream.length.toUInt64)] ++
  (π.stream.zipIdx.flatMap fun (x, i) ↦ [(1 + 2 * i, (x.limb 0).lane), (2 + 2 * i, (x.limb 1).lane)]) ++
  [(streamEnd L, π.openings.length.toUInt64)] ++
  π.openings.zipIdx.flatMap fun (ph, k) ↦
    let base := phaseBase L k
    let h := (ph.head?.map (·.path.length)).getD 0
    let w := (ph.head?.map (·.leaf.length)).getD 0
    [(base, ph.length.toUInt64), (base + 1, h.toUInt64), (base + 2, w.toUInt64)] ++
    ph.zipIdx.flatMap fun (o, j) ↦
      let ob := base + 3 + j * openingWords
      [(ob, o.leafIndex.toUInt64)] ++ o.leaf.zipIdx.map (fun (x, t) ↦ (ob + 1 + t, x.lane)) ++
      o.path.zipIdx.flatMap fun (d, dd) ↦
        d.toList.zipIdx.map fun (v, l) ↦ (ob + 1 + wireMaxLeafWords + 4 * dd + l, v)

/-- The initial machine state. -/
def initState (L : Nat) (bytecode : List K) (pub : Digest) (π : Proof) : RState :=
  let ctxWords : List (Nat × UInt64) := (List.range ctxEnd).map fun k ↦
    (k, if k = ctxWireLen then L.toUInt64 else if k = ctxBytecode then bcA
      else if k = ctxBytecodeLen then bytecode.length.toUInt64
      else if ctxPublic ≤ k ∧ k < ctxPublic + 4 then pub.toList.getD (k - ctxPublic) 0
      else if k = ctxDecoded then decA else if k = ctxWork then workA else 0)
  RState.ofWords ctxA <|
    ctxWords.map (fun (k, v) ↦ (wd ctxA k, v)) ++
    (decodedImage L π).map (fun (k, v) ↦ (wd decA k, v)) ++
    (List.range (max workWords (bytecode.length + 2))).map (fun k ↦ (wd workA k, 0)) ++
    bytecode.zipIdx.map (fun (x, k) ↦ (wd bcA k, x.lane))

/-- Set registers. -/
def _root_.Native.Test.RState.setRegs (s : RState) (rs : List (Reg64 × UInt64)) : RState :=
  { s with regs := rs.foldl (fun regs (r, v) ↦ regs.set! (regIdx r) v) s.regs }

/-- Run a gadget: `some (true, s)` if it ends normally, `some (false, s)` if it rejects. -/
def gadget (c : Stmt) (s : RState) : Option (Bool × RState) :=
  match Native.Test.run 100000000 c s with
  | some (.ok s, _) => some (true, s)
  | some (.err s, _) => some (false, s)
  | none => none

/-- An operation's gadget: its words, `none` on rejection; `panic` if stuck. -/
def runOp (s : RState) : Op → Option (List UInt64 × RState)
  | .read => do
    let (ok, s) ← gadget readScalar s
    if ok then some ([s.regs[regIdx .r9]!, s.regs[regIdx .r10]!], s) else none
  | .sample => do
    let (ok, s) ← gadget sampleChallenge s
    if ok then some ([s.regs[regIdx .r9]!, s.regs[regIdx .r10]!], s) else none
  | .grind bits => do
    let (ok, s) ← gadget grind (s.setRegs [(.rsi, bits.toUInt64)])
    if ok then some ([], s) else none
  | .commit h w => do
    let (ok, s) ← gadget commit (s.setRegs [(.rsi, h.toUInt64), (.rbx, w.toUInt64)])
    if ok then some ([], s) else none
  | .query i ps => do
    let m := ps.zipIdx.foldl (fun m (p, j) ↦ m.insert (wd posA j) p.toUInt64) s.mem
    let m := (List.range (ps.length * wireMaxLeafWords)).foldl (fun m j ↦ m.insert (wd outA j) 0) m
    let s := { s with mem := m }
    let (ok, s) ← gadget query (s.setRegs [(.r9, i.toUInt64), (.r10, posA),
      (.r11, ps.length.toUInt64), (.r12, outA)])
    if ok then
      let w := (s.word (wd ctxA (qRootW + 5))).toNat
      some ((List.range (ps.length * w)).map fun j ↦ s.word (wd outA j), s)
    else none

/-- The gadgets' answer. -/
def codeRun (L : Nat) (bytecode : List K) (pub : Digest) (π : Proof) (ops : List Op) :
    Option (List (List UInt64) × Bool) := Id.run do
  let some (true, s) := gadget seed (initState L bytecode pub π) | return none
  let mut s := s
  let mut outs := []
  for o in ops do
    match runOp s o with
    | some (ws, s') => s := s'; outs := outs ++ [ws]
    | none => return none
  match gadget finish s with
  | some (ok, _) => return some (outs, ok)
  | none => return none

/-- The seed gadget's sponge lanes against `spongeSeedWith`. -/
def seedAgrees (L : Nat) (bytecode : List K) (pub : Digest) (π : Proof) : Bool :=
  match gadget seed (initState L bytecode pub π) with
  | some (true, s) =>
    (List.range 25).map (fun i ↦ s.word (wd ctxA (laneW + i))) ==
      (Id.run (spongeSeedWith (m := Id) keccakF1600 bytecode pub)).toList
  | _ => false

def agree (L : Nat) (bytecode : List K) (pub : Digest) (π : Proof) (ops : List Op) : Bool :=
  codeRun L bytecode pub π ops == specRun bytecode pub π ops

/-! ## A synthetic proof -/

def kw (n : Nat) : K := K.ofLane (n * 0x9e3779b97f4a7c15 + 0x0123456789abcdef).toUInt64

def leaves : List (List K) := (List.range 4).map fun i ↦ (List.range 3).map fun t ↦ kw (10 * i + t)

def leafDigest (l : List K) : Digest := keccak256 (l.flatMap K.toBytes)

def node (a b : Digest) : Digest := keccak256 (digestBytes a ++ digestBytes b)

def level1 : List Digest := (leaves.map leafDigest).toChunks 2 |>.map fun c ↦ node c[0]! c[1]!

def root : Digest := node level1[0]! level1[1]!

def opening (q : Nat) : Opening :=
  ⟨q, leaves[q]!, [leafDigest leaves[q ^^^ 1]!, level1[(q / 2) ^^^ 1]!]⟩

def rootHalves : List E := [(digestHalves root).1, (digestHalves root).2]

def synth : Proof :=
  ⟨(List.range 3).map (fun i ↦ E.ofLimbs (kw (100 + i)) (kw (200 + i))) ++ rootHalves ++
      (List.range 40).map (fun i ↦ E.ofLimbs (kw (300 + i)) 0),
    [[opening 2, opening 0, opening 3], [opening 1]]⟩

def synthL : Nat := 16 * synth.stream.length + 5

def synthBytecode : List K := (List.range 5).map fun i ↦ kw (1000 + i)

def synthPub : Digest := #v[1, 2, 3, 0xffffffffffffffff]

def synthPrograms : List (List Op) := [
  [],
  [.read, .read, .read],
  [.sample, .read, .sample, .sample],
  [.read, .read, .read, .commit 2 3, .query 0 [2, 0, 3], .query 0 [1]],
  [.read, .read, .read, .commit 2 3, .sample, .read, .query 0 [2, 0, 3], .query 0 [1]],
  [.read, .read, .read, .commit 2 3, .query 0 [2, 0, 1]],
  [.read, .read, .read, .commit 2 3, .query 0 [2, 0]],
  [.read, .read, .read, .commit 2 4, .query 0 [2, 0, 3]],
  [.read, .read, .read, .commit 3 3, .query 0 [2, 0, 3]],
  [.read, .read, .read, .commit 2 3, .query 1 [2, 0, 3]],
  [.read, .read, .commit 2 3, .query 0 [2, 0, 3]],
  [.query 0 []],
  [.read, .read, .read, .commit 2 3, .query 0 [2, 0, 3], .query 0 [1], .query 0 []],
  [.read, .read, .read, .read, .read, .read, .read, .read, .read],
  [.grind 1, .sample, .read],
  [.read, .grind 1, .sample, .read],
  [.read, .read, .grind 1, .read],
  [.read, .read, .read, .grind 2, .sample, .sample],
  [.grind 64, .sample],
  [.grind 70, .read],
  [.read, .read, .read, .read, .grind 1, .grind 1, .sample],
  [.read, .read, .read, .read, .read, .read, .grind 1, .sample, .read],
  [.read, .read, .read, .commit 2 3, .query 0 [2, 0, 3], .query 0 [1]] ++ List.replicate 40 .read,
  [.read, .read, .read, .commit 2 3, .query 0 [2, 0, 3]] ++ List.replicate 40 .read]

#guard seedAgrees synthL synthBytecode synthPub synth
#guard synthPrograms.all (agree synthL synthBytecode synthPub synth)
-- Both outcomes occur.
#guard synthPrograms.any fun p ↦ (specRun synthBytecode synthPub synth p).isSome
#guard synthPrograms.any fun p ↦ (specRun synthBytecode synthPub synth p).isNone
#guard synthPrograms.any fun p ↦ (specRun synthBytecode synthPub synth p).map (·.2) == some true

end NativeVm.Test.TranscriptTest
