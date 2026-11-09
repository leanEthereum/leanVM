import LeanVM.Guest.Hints
import LeanVM.Guest.Limits
import LeanVM.Guest.Interp
import LeanVM.Guest.Renumber
import LeanVM.Guest.Expand
import LeanVM.Guest.Data.Source
import Statement.Data.Bytecode
import LeanVM.Guest.Code
import LeanVM.Guest.B1.Da.DualMath
import LeanVM.Cli.Common

/-!
# `guest-diff`: the guest's mirror and hint generator against Rust executions

`lake exe guest-diff <case>...` reads cases written by the exporter's ignored test `guest_diff`
(`scripts/guest-export/src/export/guest_diff.rs`, format `leanvm-guest-diff 4`): a real
aggregation's statement `s`, seed, node witness `w`, the streams `aggregate` installed (captured
through the test-only `FORGE` hook, `aggregation/hints.rs:53`) and its public input. For each
case it checks

* that `w` holds `s` (`NodeRelation`'s computable parts: every child's proof verifies, every raw
  signature verifies and every signature claim is a raw signature's or a child's, the DA digest is that of the claim the directly checked matrix opens, else zero or
  a child's, the batching closes, the shapes), within the deployed limits (`Limits`' parts) and
  with no zero challenge where the guest divides (`NoZeroChallenge`: `verifyDeferredNZ` accepts
  every child's proof);
* (i) that `Hints.honestStreams` is the Rust streams, stream by stream and entry by entry;
* (iii) that the public input is `statementDigest seed s`;
* (ii) that the interpreter accepts the guest's core IR (`coreProgram`: the renumbered expansion
  of the source, which `guest-core --check` keeps equal to the data) on `main`, with the honest
  streams and that public input, and consumes every stream.

It prints the first divergence of each check and exits with `1` if any check fails.
-/

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest
open LeanVM.Guest.Hints LeanVM.Guest.Coverage LeanVM.Guest.Interp LeanVM.Cli

namespace GuestDiff

/-! ## Reading a case -/

/-- A reader over the case's tokens. -/
abbrev R := ReaderT (Array String) (StateT Nat (Except String))

def tok : R String := do
  let i ← get
  let some t := (← read)[i]? | throw s!"the case ends at token {i}"
  set (i + 1)
  return t

def expect (t : String) : R Unit := do
  let u ← tok
  if u != t then throw s!"expected `{t}` at token {(← get) - 1}, found `{u}`"

def nat : R Nat := do
  let t ← tok
  let some n := t.toNat? | throw s!"`{t}` is not a number"
  return n

def hexOf (t : String) : Option Nat :=
  t.foldl (fun acc c => do return 16 * (← acc) + (← hexDigit? c)) (some 0)

def hex : R Nat := do
  let t ← tok
  let some n := hexOf t | throw s!"`{t}` is not hex"
  return n

def many {α : Type} (item : R α) : R (List α) := do
  let n ← nat
  (List.range n).mapM fun _ => item

def eR : R E := do return word (← hex) (← hex) (← hex)

def kR : R K := do return K.ofBits (← hex)

def bytesR : R (List UInt8) := do
  let t ← tok
  let cs := t.toList
  if cs.length % 2 != 0 then throw s!"`{t}` is not bytes"
  (List.range (cs.length / 2)).mapM fun i => do
    let some hi := hexDigit? cs[2 * i]! | throw s!"`{t}` is not bytes"
    let some lo := hexDigit? cs[2 * i + 1]! | throw s!"`{t}` is not bytes"
    return (16 * hi + lo).toUInt8

def digestR : R Digest := do return digestOfBytes (← bytesR)

def d128 : R (BitVec 128) := do return bitsLE 128 ((← bytesR).map (·.toNat))

/-- A key as its 32 bytes, split in halves, and a message: a leanXMSS key is its root then its
parameter, a leanSPHINCS key `PK.seed` then `PK.root` (`to_bytes`). -/
def claimR : R ((BitVec 128 × BitVec 128) × BitVec 256) := do
  let pk := (← bytesR).map (·.toNat)
  let m := (← bytesR).map (·.toNat)
  return ((bitsLE 128 (pk.take 16), bitsLE 128 (pk.drop 16)), bitsLE 256 m)

def deferR : R DeferredClaim := do
  expect "defer"
  return ⟨← many eR, ← eR⟩

def statementR : R NodeStatement := do
  expect "xmss"
  let xmss ← many do let ((r, p), m) ← claimR; return ((⟨r, p⟩ : HashSig.PublicKey), m)
  expect "sphincs"
  let sphincs ← many do let ((p, r), m) ← claimR; return ((⟨p, r⟩ : Sphincs.PublicKey), m)
  expect "da"
  let da ← digestR
  return ⟨⟨xmss, sphincs, da⟩, ← deferR⟩

def childR : R Child := do
  expect "child"
  let statement ← statementR
  expect "fresh"
  let fresh : BytecodeClaim := ⟨← many eR, ← eR⟩
  expect "proof"
  let stream ← many eR
  let openings ← many do many do return (⟨← nat, ← many kR, ← many digestR⟩ : Opening)
  return ⟨statement, fresh, ⟨stream, openings⟩⟩

def fn128 {n : Nat} (xs : List (BitVec 128)) : Fin n → BitVec 128 := fun i => xs.getD i 0

def xmssSigR : R LeanXmss.Signature := do
  let index ← nat
  let layer : R LeanXmss.LayerSignature := do
    return ⟨← d128, fn128 (← many d128), fn128 (← many d128)⟩
  let bottom ← layer
  let top ← layer
  return ⟨⟨index % 2 ^ 32, Nat.mod_lt _ (by decide)⟩, fun l => if l.val = 0 then bottom else top⟩

def sphincsSigR : R Sphincs.Signature := do
  let randomizer ← d128
  let fors ← (List.range Sphincs.forsTreeCount).mapM fun _ => do
    return (⟨← d128, fn128 (← many d128)⟩ : Sphincs.ForsTreeOpening)
  let layers ← (List.range Sphincs.layerCount).mapM fun _ => do
    return (BitVec.ofNat 32 (← nat), (← many d128), (← many d128))
  let layer := fun (l : Sphincs.Layer) =>
    let (counter, values, path) := layers.getD l.val (0, [], [])
    (⟨counter, fn128 values, fn128 path⟩ : Sphincs.LayerSignature l)
  return ⟨randomizer, fun c => fors.getD c ⟨0, fun _ => 0⟩, layer⟩

/-- A raw leanXMSS signature with its claim. -/
def rawXmssR : R (LeanXmssClaim × LeanXmss.Signature) := do
  let ((r, p), m) ← claimR
  return (((⟨r, p⟩ : HashSig.PublicKey), m), ← xmssSigR)

/-- A raw leanSPHINCS signature with its claim. -/
def rawSphincsR : R (LeanSphincsClaim × Sphincs.Signature) := do
  let ((p, r), m) ← claimR
  return (((⟨p, r⟩ : Sphincs.PublicKey), m), ← sphincsSigR)

def daWitnessR : R LeanVM.Da.MatrixWitness := do return ⟨← many (many kR)⟩

/-- The blob matrix checked directly, with the DA claim it opens (`NodeWitness.daMatrix`): `direct`, the
root, the membership challenge, the rows; or `none`. -/
def daR : R (Option (DaClaim × LeanVM.Da.MatrixWitness)) := do
  match ← tok with
  | "direct" =>
    let claim := DaClaim.mk (← digestR) (← eR)
    return some (claim, ← daWitnessR)
  | "none" => return none
  | t => throw s!"`{t}` is no DA witness"

/-- A case. -/
structure Case where
  name : String
  seed : Digest
  logMemory : Nat
  publicInput : List E
  statement : NodeStatement
  witness : NodeWitness
  streams : Streams

def caseR : R Case := do
  expect "leanvm-guest-diff"; expect "4"
  expect "case"; let name ← tok
  expect "seed"; let seed ← digestR
  expect "log_memory"; let logMemory ← nat
  expect "public_input"; let publicInput ← many eR
  expect "statement"; let statement ← statementR
  expect "children"; let children ← many childR
  expect "raw_xmss"; let xmss ← many rawXmssR
  expect "raw_sphincs"; let sphincs ← many rawSphincsR
  expect "da_witness"; let da ← daR
  expect "batch"
  let pairs := fun (xs : List E) => (List.range (xs.length / 2)).map fun i => (xs[2 * i]!, xs[2 * i + 1]!)
  let bc ← many eR
  let stars ← many eR
  let hints : BatchingHints := ⟨pairs bc, stars.getD 0 0⟩
  expect "streams"
  let streams ← many do
    expect "stream"
    let n ← tok
    return (n, ← many (many eR))
  expect "end"
  return ⟨name, seed, logMemory, publicInput, statement, ⟨children, xmss, sphincs, da, hints⟩, streams⟩

def readCase (path : System.FilePath) : IO Case := do
  let text ← IO.FS.readFile path
  let toks := (((text.split Char.isWhitespace).toList.map (·.toString)).filter (· != "")).toArray
  match (caseR.run toks).run' 0 with
  | .ok c => return c
  | .error e => throw (IO.userError s!"{path}: {e}")

/-! ## The checks -/

/-- The bytecode the verifier reads the length of: `2^23` words, those of `logSize = 19`. -/
def bytecode : List K := List.replicate (2 ^ (Data.logSize + busBits)) 0

/-- `MatrixWitness.Opens`, its dot products computed and its commitment computed level by level as
the crate does (`lean_da`'s `LeanDa.commitCodewords`, on codewords of `2^15` symbols the statement's
`commitCells` of the matrix they form: `LeanDa.commitCodewords_eq_commitCells`), the dual codeword
of `z` as `dualAt` (`LeanDa.dualCodewordAt`: `Guest.B1.Da.dualAt_eq`). -/
def daOpens (root : Digest) (z : E) (w : LeanVM.Da.MatrixWitness) : Bool :=
  let dual := (List.range (2 ^ LeanDa.logM)).map (LeanVM.Guest.B1.Da.dualAt z)
  1 ≤ w.rows.length && w.rows.length ≤ LeanDa.maxRows &&
    w.rows.all (·.length == 2 ^ LeanDa.logM) &&
    (LeanDa.commitCodewords keccakF1600 w.rows).toList == (LeanVM.Protocol.Digest.toBytes root).toList &&
    w.rows.all fun row => (dual.zip row).foldl (fun acc (v, x) => acc + v * ofK x) 0 == 0

/-- Every raw signature of a kind verifies, and every claim of the kind is a raw signature's or in
a child's list, each by name. -/
def held {α W : Type} [BEq α] (children : List Child) (kind : String) (claims : List α)
    (raws : List (α × W)) (verifies : α → W → Bool) (inChild : Child → α → Bool) :
    List (String × Bool) :=
  raws.zipIdx.map (fun ((claim, σ), i) => (s!"{kind} raw signature {i} verifies", verifies claim σ)) ++
    claims.zipIdx.map fun (claim, i) => (s!"{kind} claim {i} held",
      raws.any (·.1 == claim) || children.any (inChild · claim))

def digestEq (a b : Digest) : Bool := a.toList == b.toList

/-- `NodeRelation`'s computable parts, each by name. -/
def nodeRel (c : Case) : List (String × Bool) :=
  let s := c.statement
  let w := c.witness
  let shaped := fun (d : DeferredClaim) => d.bytecodePoint.length == Nat.log2 bytecode.length
  [("the statement's deferred claim is shaped", shaped s.deferredClaim)] ++
  w.children.zipIdx.flatMap (fun (ch, i) =>
    [(s!"child {i}'s deferred claim is shaped", shaped ch.statement.deferredClaim),
      (s!"child {i}'s proof verifies", verifyDeferred bytecode c.seed (statementDigest c.seed ch.statement)
        ch.freshClaim ch.proof)]) ++
  held w.children "leanXMSS" s.claims.xmss w.xmssSignatures (fun cl σ
      => LeanXmss.verifyWithKeccak cl.1 cl.2 σ)
    (fun ch cl => ch.statement.claims.xmss.any (· == cl)) ++
  held w.children "leanSPHINCS" s.claims.sphincs w.sphincsSignatures (fun cl σ
      => Sphincs.verifyWithKeccak cl.1 cl.2 σ)
    (fun ch cl => ch.statement.claims.sphincs.any (· == cl)) ++
  (match w.daMatrix with
    | some (cl, m) =>
      [("the DA digest is the directly checked claim's", digestEq s.claims.daDigest
          (daClaimDigest cl)),
        ("the directly checked matrix opens its claim", daOpens cl.daRoot cl.membershipChallenge m)]
    | none =>
      [("the DA digest is zero or a child's", digestEq s.claims.daDigest zeroDigest ||
        w.children.any fun ch => digestEq ch.statement.claims.daDigest s.claims.daDigest)]) ++
  [if w.children = [] then
      ("the leaf defers the bytecode at zero", s.deferredClaim.bytecodePoint.all (· == 0))
    else ("the batching defers the statement's claim",
      (batch (w.children.map fun ch => ⟨statementDigest c.seed ch.statement, ch.freshClaim, ch.statement.deferredClaim⟩)
        w.batchingHints).map DeferredClaim.cells == some s.deferredClaim.cells)]

/-- `Limits`' parts and `NoZeroChallenge`, each by name. -/
def limits (c : Case) : List (String × Bool) :=
  let s := c.statement
  let w := c.witness
  let rawX := w.xmssSignatures
  let rawS := w.sphincsSignatures
  w.children.zipIdx.flatMap (fun (ch, i) => ([(s!"child {i}'s stack log is at least {minChildStackLog}",
        match announcedLayoutAndRate bytecode ch.proof.stream with
        | some (layout, _) => decide (minChildStackLog ≤ layout.stackLog)
        | none => true),
      (s!"child {i}'s stream is at most {childStreamCap} scalars", ch.proof.stream.length ≤ childStreamCap),
      (s!"child {i}'s proof has no zero challenge where the guest divides",
        Limits.verifyDeferredNZ bytecode c.seed (statementDigest c.seed ch.statement) ch.freshClaim ch.proof),
      (s!"child {i}'s lists are below 2^16", ch.statement.claims.xmss.length < 2 ^ 16 &&
        ch.statement.claims.sphincs.length < 2 ^ 16)] : List (String × Bool))) ++
  ([("leanXMSS claims held as often as declared", s.claims.xmss.all fun x =>
      s.claims.xmss.count x ≤ (rawX.map (·.1)).count x +
        (w.children.map fun ch => ch.statement.claims.xmss.count x).sum),
    ("leanSPHINCS claims held as often as declared", s.claims.sphincs.all fun x =>
      s.claims.sphincs.count x ≤ (rawS.map (·.1)).count x +
        (w.children.map fun ch => ch.statement.claims.sphincs.count x).sum),
    ("at most 16 children", w.children.length ≤ 16),
    ("the coverage table below 2^16", coverageSlots w < 2 ^ 16)] :
    List (String × Bool))

def showLimbs (x : E) : String :=
  let (c0, c1, c2) := limbsOf x
  s!"({c0}, {c1}, {c2})"

/-- The first difference of two streams, if any. -/
def entryDiff (a b : List Entry) : Option String :=
  if a.length != b.length then some s!"{a.length} entries, Rust {b.length}" else
  (a.zip b).zipIdx.findSome? fun ((x, y), i) =>
    if x.length != y.length then some s!"entry {i}: {x.length} values, Rust {y.length}" else
    (x.zip y).zipIdx.findSome? fun ((u, v), j) =>
      if u == v then none else some s!"entry {i}, value {j}: {showLimbs u}, Rust {showLimbs v}"

/-- (i): every stream, against Rust's; and the streams' order of first push. -/
def streamDiffs (lean rust : Streams) : List String :=
  let names := (lean.map (·.1) ++ rust.map (·.1)).eraseDups
  let diffs := names.filterMap fun n =>
    match lean.lookup n, rust.lookup n with
    | some a, some b => (entryDiff a b).map (s!"stream `{n}`: " ++ ·)
    | some a, none => some s!"stream `{n}`: {a.length} entries, none in Rust"
    | none, some b => some s!"stream `{n}`: none, {b.length} entries in Rust"
    | none, none => none
  if diffs.isEmpty && lean.map (·.1) != rust.map (·.1) then
    [s!"the streams' order: {lean.map (·.1)}, Rust {rust.map (·.1)}"]
  else diffs

/-- The interpreter's discrete logarithm: a table below `2^16`, else Pohlig-Hellman. -/
def dlogOf (t : DlogTables) (small : Std.HashMap Nat Nat) (a : K) : Option Nat :=
  match small[keyOf a]? with
  | some n => some n
  | none => dlogWith t a

/-- `g^i ↦ i` below `2^16`. -/
def smallLogs : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := {}
  let mut x : K := 1
  for i in List.range (2 ^ 16) do
    m := m.insert (keyOf x) i
    x := x * g
  return m

/-- (ii): run `main` of the core IR; the error, or the streams left unread. -/
def runGuest (program : Core.Program) (c : Case) (streams : Streams) (pi : List E) :
    Option String :=
  let tables := DlogTables.build
  let small := smallLogs
  let cfg : Cfg := {
    program
    initMem := fun a => if a == gpowK 0 then pi[0]? else if a == gpowK 1 then pi[1]? else none
    logMem := c.logMemory
    dlog := dlogOf tables small
    streams }
  match run cfg "main" [] with
  | .error e => some e
  | .ok (_, st) =>
    match st.streams.filter (·.2 != []) with
    | [] => none
    | left => some s!"streams left unread: {left.map fun (n, es) => s!"`{n}` ({es.length})"}"

end GuestDiff

open GuestDiff

/-- A value and the milliseconds it took. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let start ← IO.monoMsNow
  let a ← IO.lazyPure f
  return (a, (← IO.monoMsNow) - start)

/-- The driver: `guest-diff [--no-rel] [--no-run] <case>...`; the flags skip the witness check and
the run. -/
def main (args : List String) : IO UInt32 := do
  let (flags, paths) := args.partition (·.startsWith "--")
  if paths.isEmpty || flags.any (· ∉ ["--no-rel", "--no-run"]) then
    IO.eprintln "usage: guest-diff [--no-rel] [--no-run] <case>..."
    return 2
  let program ← match Expand.expandProgram Data.guest with
    | .ok fns => pure (fns.map Core.Fn.renumber)
    | .error e => throw (IO.userError s!"expansion: {e}")
  let mut failed := false
  for path in paths do
    let start ← IO.monoMsNow
    let c ← readCase path
    IO.println s!"case {c.name} ({path}): {c.witness.children.length} children, \
      {c.statement.claims.xmss.length} leanXMSS, {c.statement.claims.sphincs.length} leanSPHINCS, \
      {if c.witness.daMatrix.isSome then "a blob matrix" else "no blob matrix"}, DA digest \
      {if c.statement.claims.daDigest == zeroDigest then "zero" else "nonzero"}, read in {(← IO.monoMsNow) - start} ms"
    let report := fun (what : String) (problem : Option String) (time : Nat) => do
      match problem with
      | none => IO.println s!"  {what}: ok ({time} ms)"
      | some p => IO.println s!"  {what}: FAILED ({time} ms): {p}"
      (← IO.getStdout).flush
      return problem.isSome
    if "--no-rel" ∉ flags then
      let (bad, time) ← timed fun _ => ((nodeRel c).find? (!·.2)).map (·.1 ++ " fails")
      failed := (← report "the witness holds the statement" bad time) || failed
      let (badL, timeL) ← timed fun _ => ((limits c).find? (!·.2)).map (·.1 ++ " fails")
      failed := (← report "the witness is within the limits, no zero challenge" badL timeL) || failed
    let (streams, time) ← timed fun _ => honestStreams bytecode c.seed c.statement c.witness
    let (diff, time') ← timed fun _ => (streamDiffs streams c.streams).head?
    failed := (← report "(i) the honest streams are Rust's" diff (time + time')) || failed
    let pi := publicInput c.seed c.statement
    failed := (← report "(iii) the public input is the statement's digest"
      (if pi == c.publicInput then none
        else some s!"{pi.map showLimbs}, Rust {c.publicInput.map showLimbs}") 0) || failed
    if "--no-run" ∉ flags then
      let (problem, time) ← timed fun _ => runGuest program c streams pi
      failed := (← report "(ii) the interpreter runs main" problem time) || failed
  return if failed then 1 else 0
