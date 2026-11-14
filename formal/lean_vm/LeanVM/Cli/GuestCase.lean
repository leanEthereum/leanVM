/-
  LeanVM.Cli.GuestCase

  The reader of the guest's test cases (`scripts/guest-export`'s `guest_diff`, format `leanvm-guest-diff 4`),
  shared by `guest-diff` and `guest-run`. No proof imports it.
-/

module

public import LeanVM.Guest.Hints
public import LeanVM.Cli.Common

@[expose] public section

namespace LeanVM.Cli.GuestCase

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node LeanVM.Guest
open LeanVM.Guest.Hints LeanVM.Guest.Coverage LeanVM.Cli

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

def eR : R E := do return word (← hex) (← hex)

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
  -- The lambda grind's nonce leads `bc_sumcheck_msgs`; a leaf batches nothing.
  let hints : BatchingHints := match bc with
    | nonce :: rounds => ⟨nonce, pairs rounds, stars.getD 0 0⟩
    | [] => ⟨0, [], stars.getD 0 0⟩
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

end LeanVM.Cli.GuestCase
