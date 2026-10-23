import LeanVM.Guest.Hints
import LeanVM.Guest.Interp
import LeanVM.Guest.Renumber
import LeanVM.Guest.Expand
import LeanVM.Guest.Data.Source

/-!
# `guest-diff`: the guest's mirror and hint generator against Rust executions

`lake exe guest-diff <case>...` reads cases written by the Rust test `guest_diff`
(`crates/rec_aggregation/src/aggregation/guest_diff.rs`): a real aggregation's statement `s`, seed,
node witness `w`, the streams `aggregate` installed and its public input. For each case it checks

* that `w` holds `s` (`NodeRel`'s computable parts: every child's proof verifies, every claim is
  held, the batching closes, the shapes);
* (i) that `Hints.honestStreams` is the Rust streams, stream by stream and entry by entry;
* (iii) that the public input is `statementDigest seed s`;
* (ii) that the interpreter accepts the guest's core IR (`coreProgram`: the renumbered expansion
  of the source, which `guest-core --check` keeps equal to the data) on `main`, with the honest
  streams and that public input, and consumes every stream.

It prints the first divergence of each check and exits with `1` if any check fails.
-/

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest LeanVM.Guest.Hints LeanVM.Guest.Interp

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

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none

def hexOf (t : String) : Option Nat :=
  t.foldl (fun acc c => do return 16 * (← acc) + (← hexDigit c)) (some 0)

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
    let some hi := hexDigit cs[2 * i]! | throw s!"`{t}` is not bytes"
    let some lo := hexDigit cs[2 * i + 1]! | throw s!"`{t}` is not bytes"
    return (16 * hi + lo).toUInt8

/-- A little-endian bit vector of bytes. -/
def bitsOf (n : Nat) (b : List UInt8) : BitVec n :=
  BitVec.ofNat n (b.foldr (fun x acc => x.toNat + 256 * acc) 0)

def digestR : R Digest := do return digestOfBytes (← bytesR)

def d128 : R (BitVec 128) := do return bitsOf 128 (← bytesR)

/-- A key as its 32 bytes, root then parameter, and a message. -/
def claimR : R ((BitVec 128 × BitVec 128) × BitVec 256) := do
  let pk ← bytesR
  let m ← bytesR
  return ((bitsOf 128 (pk.take 16), bitsOf 128 (pk.drop 16)), bitsOf 256 m)

def deferR : R DeferredClaim := do
  expect "defer"
  return ⟨← many eR, ← eR, ← many eR, ← eR, ← eR⟩

def statementR : R NodeStatement := do
  expect "xmss"
  let xmss ← many do let ((r, p), m) ← claimR; return ((⟨r, p⟩ : LeanXmss.PublicKey), m)
  expect "sphincs"
  let sphincs ← many do let ((r, p), m) ← claimR; return ((⟨r, p⟩ : Sphincs.PublicKey), m)
  expect "da"
  let da ← many do return (← digestR, ← digestR)
  return ⟨⟨xmss, sphincs, da⟩, ← deferR⟩

def childR : R Child := do
  expect "child"
  let statement ← statementR
  expect "fresh"
  let fresh : FixedClaims := ⟨← many eR, ← eR, ← eR, ← eR, ← many eR, ← many eR, ← many eR, ← eR⟩
  expect "proof"
  let stream ← many eR
  let openings ← many do return (⟨← many kR, ← many digestR⟩ : Opening)
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
  let randomness ← d128
  let forest ← (List.range Sphincs.forestCoords).mapM fun _ => do
    let subs ← (List.range 2).mapM fun _ => do
      return (⟨fn128 (← many d128), fn128 (← many d128)⟩ : Sphincs.SubOpening)
    return (⟨fun j => subs.getD j ⟨fun _ => 0, fun _ => 0⟩, fn128 (← many d128)⟩ : Sphincs.CoordOpening)
  let counter ← nat
  let values ← many d128
  let path ← many d128
  return ⟨randomness, fun c => forest.getD c ⟨fun _ => ⟨fun _ => 0, fun _ => 0⟩, fun _ => 0⟩,
    fun _ => ⟨BitVec.ofNat 32 counter, fn128 values, fn128 path⟩⟩

def holderR {W : Type} (direct : R W) : R (Holder W) := do
  match ← tok with
  | "direct" => return .direct (← direct)
  | "child" => return .child (← nat)
  | t => throw s!"`{t}` is no holder"

def daWitnessR : R LeanVM.Da.Witness := do return ⟨← many (many kR), ← many eR⟩

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
  expect "leanvm-guest-diff"; expect "1"
  expect "case"; let name ← tok
  expect "seed"; let seed ← digestR
  expect "log_memory"; let logMemory ← nat
  expect "public_input"; let publicInput ← many eR
  expect "statement"; let statement ← statementR
  expect "children"; let children ← many childR
  expect "holders_xmss"; let xmss ← many (holderR xmssSigR)
  expect "holders_sphincs"; let sphincs ← many (holderR sphincsSigR)
  expect "holders_da"; let da ← many (holderR daWitnessR)
  expect "batch"
  let pairs := fun (xs : List E) => (List.range (xs.length / 2)).map fun i => (xs[2 * i]!, xs[2 * i + 1]!)
  let bc ← many eR
  let mat ← many eR
  let stars ← many eR
  let hints : BatchHints := ⟨pairs bc, pairs mat, stars.getD 0 0, stars.getD 1 0, stars.getD 2 0⟩
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

/-- The bytecode the verifier reads the length of: `2^22` words, those of `BYTECODE_LOG = 18`. -/
def bytecode : List K := List.replicate (2 ^ (Data.bytecodeLog + busBits)) 0

/-- `Witness.Opens`, its dot products computed. -/
def daOpens (root vd : Digest) (w : LeanVM.Da.Witness) : Bool :=
  1 ≤ w.rows.length && w.rows.length ≤ LeanDa.maxRows &&
    w.rows.all (·.length == 2 ^ LeanDa.logM) &&
    LeanDa.commitCodewords LeanVM.Da.blake2s w.rows == LeanVM.Da.toBytes root &&
    w.vector.length == 2 ^ LeanDa.logM && LeanDa.vectorDigest LeanVM.Da.blake2s w.vector == LeanVM.Da.toBytes vd &&
    w.rows.all fun row => (w.vector.zip row).foldl (fun acc (v, x) => acc + v * ofK x) 0 == 0

/-- Every claim of a kind is held, each by name. -/
def held {α W : Type} (children : List Child) (kind : String) (claims : List α)
    (holders : List (Holder W)) (direct : α → W → Bool) (inChild : Child → α → Bool) :
    List (String × Bool) :=
  (s!"{kind} holders", claims.length == holders.length) ::
    ((claims.zip holders).zipIdx.map fun ((claim, h), i) => match h with
      | .direct σ => (s!"{kind} claim {i} held directly", direct claim σ)
      | .child j => (s!"{kind} claim {i} held by child {j}",
          (children[j]?.map (inChild · claim)).getD false))

/-- `NodeRel`'s computable parts, each by name. -/
def nodeRel (c : Case) : List (String × Bool) :=
  let s := c.statement
  let w := c.witness
  let shaped := fun (d : DeferredClaim) =>
    d.bytecodePoint.length == Nat.log2 bytecode.length && d.matrixPoint.length == 2 * blake2sR1csLogSize
  [("the statement's deferred claim is shaped", shaped s.defer)] ++
  w.children.zipIdx.flatMap (fun (ch, i) =>
    [(s!"child {i}'s deferred claim is shaped", shaped ch.statement.defer),
      (s!"child {i}'s proof verifies", verifyDeferred bytecode c.seed (statementDigest c.seed ch.statement)
        ch.fresh ch.proof)]) ++
  held w.children "leanXMSS" s.claims.xmss w.xmss (fun cl σ => xmssVerify cl.1 cl.2 σ)
    (fun ch cl => ch.statement.claims.xmss.any (· == cl)) ++
  held w.children "leanSPHINCS" s.claims.sphincs w.sphincs (fun cl σ => sphincsVerify cl.1 cl.2 σ)
    (fun ch cl => ch.statement.claims.sphincs.any (· == cl)) ++
  held w.children "DA" s.claims.da w.da (fun cl d => daOpens cl.1 cl.2 d)
    (fun ch cl => ch.statement.claims.da.any (· == cl)) ++
  [if w.children = [] then
      ("the leaf defers the polynomials at zero", s.defer.bytecodePoint.all (· == 0) &&
        s.defer.matrixPoint.all (· == 0))
    else ("the batching defers the statement's claim",
      (batch (w.children.map fun ch => ⟨statementDigest c.seed ch.statement, ch.fresh, ch.statement.defer⟩)
        w.hints).map DeferredClaim.cells == some s.defer.cells)]

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

/-- (i): every stream, against Rust's. -/
def streamDiffs (lean rust : Streams) : List String :=
  let names := (lean.map (·.1) ++ rust.map (·.1)).eraseDups
  names.filterMap fun n =>
    match lean.lookup n, rust.lookup n with
    | some a, some b => (entryDiff a b).map (s!"stream `{n}`: " ++ ·)
    | some a, none => some s!"stream `{n}`: {a.length} entries, none in Rust"
    | none, some b => some s!"stream `{n}`: none, {b.length} entries in Rust"
    | none, none => none

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
      {c.statement.claims.da.length} DA claims, read in {(← IO.monoMsNow) - start} ms"
    let report := fun (what : String) (problem : Option String) (time : Nat) => do
      match problem with
      | none => IO.println s!"  {what}: ok ({time} ms)"
      | some p => IO.println s!"  {what}: FAILED ({time} ms): {p}"
      (← IO.getStdout).flush
      return problem.isSome
    if "--no-rel" ∉ flags then
      let (bad, time) ← timed fun _ => ((nodeRel c).find? (!·.2)).map (·.1 ++ " fails")
      failed := (← report "the witness holds the statement" bad time) || failed
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
