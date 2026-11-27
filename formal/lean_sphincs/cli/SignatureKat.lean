module

public import Statement.LeanSphincs

@[expose] public section

/-!
# The crate's known answers against the statement's leanSPHINCS

`signature-kat DIR` runs the statement's key generation, signer and verifier of leanSPHINCS,
compiled over Keccak-f[1600], on the EthLib test vectors the crate vendors (`DIR` is this
repository's `crates`, the vectors `lean_sphincs/tests/lean_sphincs/ethlib`: the `key_gen`, `sign`
and `verify` cases) and on leanSPHINCS's known answer
(`crates/lean_sphincs/tests/lean_sphincs/known_answer.hex`, given as a second argument): the bytes
must match. An input of the wrong length is rejected (`null`). Each case prints `ok` or `MISMATCH`;
the exit code is the number of mismatches. leanXMSS's are `lean_vm`'s `scheme-vectors`.
-/
open HashSig

namespace SignatureKat

/-- Keccak-f[1600] as a computation of the state monad: under `Id` the compiler duplicates the pure
bindings of the scheme's `do` blocks (each derivation recomputed at each use), so the
cases run the statement's definitions over `StateM Unit`, whose binds it keeps. -/
def keccak (state : LeanVM.Semantics.KeccakState) : StateM Unit LeanVM.Semantics.KeccakState :=
  pure (LeanVM.Semantics.keccakF1600 state)

/-! ## Bytes -/

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

partial def hexBytes (s : String) : Option (List UInt8) :=
  let s : String := if s.startsWith "0x" then (s.drop 2).toString else s
  let rec go : List Char → Option (List UInt8)
    | [] => some []
    | a :: b :: rest => do
        let hi ← hexDigit a
        let lo ← hexDigit b
        return (UInt8.ofNat (16 * hi + lo)) :: (← go rest)
    | [_] => none
  go s.toList

def hexOf (bytes : List UInt8) : String :=
  let digit (n : Nat) : Char := "0123456789abcdef".toList[n]!
  "0x" ++ String.ofList (bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

/-- Bytes read little endian. -/
def leNat (bytes : List UInt8) : Nat := bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

def bitVecOf (n : Nat) (bytes : List UInt8) : Option (BitVec (8 * n)) :=
  if bytes.length = n then some (BitVec.ofNat (8 * n) (leNat bytes)) else none

/-- A cursor over bytes. -/
abbrev Reader := StateT (List UInt8) Option

def take (n : Nat) : Reader (BitVec (8 * n)) := do
  let bytes ← get
  if bytes.length < n then failure
  set (bytes.drop n)
  return BitVec.ofNat (8 * n) (leNat (bytes.take n))

/-- `n` bytes read big endian. -/
def takeBigEndian (n : Nat) : Reader (BitVec (8 * n)) := do
  let bytes ← get
  if bytes.length < n then failure
  set (bytes.drop n)
  return BitVec.ofNat (8 * n) (leNat (bytes.take n).reverse)

def readFin {n : Nat} {α : Type} [Inhabited α] (read : Fin n → Reader α) : Reader (Fin n → α) := do
  let values ← (List.finRange n).mapM read
  return fun i => values.getD i.val default

/-! ## leanSPHINCS -/

namespace Sphincs
open _root_.Sphincs

/-- `LeanSphincsPublicKey::to_bytes`: `PK.seed ‖ PK.root`. -/
def publicKeyBytes (publicKey : _root_.Sphincs.PublicKey) : List UInt8 :=
  publicKey.toBytes

/-- A layer: its counter, big endian, its chain values and its path (`to_bytes`). -/
def layerBytes (layer : Layer) (signature : LayerSignature layer) : List UInt8 :=
  bigEndianBytes 4 signature.counter ++
    (List.ofFn fun chain => littleEndianBytes 16 (signature.chainValues chain)).flatten ++
    (List.ofFn fun level => littleEndianBytes 16 (signature.authenticationPath level)).flatten

/-- `LeanSphincsSignature::to_bytes`: the randomizer, the FORS openings, each layer bottom first. -/
def signatureBytes (signature : Signature) : List UInt8 :=
  littleEndianBytes 16 signature.randomizer ++
    (List.ofFn fun tree => littleEndianBytes 16 (signature.forsOpening tree).secret ++
      (List.ofFn fun level => littleEndianBytes 16 ((signature.forsOpening tree).path level)).flatten
      ).flatten ++
    (List.ofFn fun layer : Layer => layerBytes layer (signature.layers layer)).flatten

instance : Inhabited ForsTreeOpening := ⟨⟨0, fun _ => 0⟩⟩

def readLayer (layer : Layer) : Reader (LayerSignature layer) := do
  let counter ← takeBigEndian 4
  let chainValues ← readFin fun _ : ChainIndex => take 16
  let path ← readFin fun _ : Fin (layerHeight layer) => take 16
  return ⟨counter, chainValues, path⟩

def readSignature : Reader Signature := do
  let randomizer ← take 16
  let fors ← readFin fun _ : ForsTreeIndex => do
    let secret ← take 16
    let path ← readFin fun _ : Fin forsTreeHeight => take 16
    return (⟨secret, path⟩ : ForsTreeOpening)
  let bottom ← readLayer 0
  let middle ← readLayer 1
  let top ← readLayer 2
  return ⟨randomizer, fors, KeyGenerationAndSigning.layerSignatures bottom middle top⟩

def signatureOf (bytes : List UInt8) : Option Signature :=
  match readSignature.run bytes with
  | some (signature, []) => some signature
  | _ => none

/-- `LeanSphincsPublicKey::from_bytes`: `PK.seed`, then `PK.root`. -/
def publicKeyOf (bytes : List UInt8) : Option _root_.Sphincs.PublicKey :=
  if bytes.length = 32 then
    some ⟨BitVec.ofNat 128 (leNat (bytes.take 16)), BitVec.ofNat 128 (leNat (bytes.drop 16))⟩
  else none

def keygen (seed : MasterSeed) : _root_.Sphincs.PublicKey :=
  ((KeyGenerationAndSigning.keygenFromSeed (m := StateM Unit) keccak seed).run' ()).1

def sign (seed : MasterSeed) (message : Message) : Option Signature :=
  (KeyGenerationAndSigning.sign (m := StateM Unit) keccak seed message).run' ()

def verify (publicKey : _root_.Sphincs.PublicKey) (message : Message) (signature : Signature) :
    Bool :=
  (Verification.verify (m := StateM Unit) keccak publicKey message signature).run' ()

end Sphincs

/-! ## The cases -/

/-- The value of `key: value` in a case file, quotes removed. -/
def field (lines : List String) (key : String) : Option String :=
  lines.findSome? fun line =>
    let line := line.trimAsciiStart.toString
    if line.startsWith (key ++ ":") then
      some ((((line.drop (key.length + 1)).trimAscii.toString).replace "'" "").replace "\"" "")
    else none

/-- The expected output: some bytes, `true`/`false`, or `none` for `null`. -/
def expected (lines : List String) : Option String :=
  match field lines "output" with
  | some "null" => none
  | other => other

def outputOf (bytes : Option (List UInt8)) : Option String := bytes.map hexOf

def bool (b : Option Bool) : Option String := b.map fun b => if b then "true" else "false"

def runCase (scheme kind : String) (lines : List String) : Option String :=
  let bytes (key : String) : Option (List UInt8) := (field lines key).bind hexBytes
  match scheme, kind with
  | "sphincs", "key_gen" => do
      let seed ← (bytes "seed").bind (bitVecOf 32)
      return hexOf (Sphincs.publicKeyBytes (Sphincs.keygen seed))
  | "sphincs", "sign" => do
      let seed ← (bytes "seed").bind (bitVecOf 32)
      let message ← (bytes "message").bind (bitVecOf 32)
      let signature ← Sphincs.sign seed message
      return hexOf (Sphincs.signatureBytes signature)
  | "sphincs", "verify" => do
      let publicKey ← (bytes "public_key").bind Sphincs.publicKeyOf
      let message ← (bytes "message").bind (bitVecOf 32)
      let signature ← (bytes "signature").bind Sphincs.signatureOf
      bool (some (Sphincs.verify publicKey message signature))
  | _, _ => none

/-- leanSPHINCS's known answer (`known_answer`, `tests/lean_sphincs/scheme.rs`): the public key
and the signature of `SK.seed[i] = 37 i + 11` and the message `m[i] = 7 i + 3`, `sign` on the
expanded key, and its verification. -/
def knownAnswer (path : System.FilePath) : IO Bool := do
  let lines := (← IO.FS.readFile path).splitOn "\n" |>.filter (· ≠ "")
  -- the constants from the file's length, so that the compiler does not evaluate the known answer
  -- as a closed term at start-up
  let (a, b) := if lines.length = 2 then (37, 7) else (0, 0)
  let seedBytes : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (a * i + 11)
  let messageBytes : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (b * i + 3)
  let seed : MasterSeed := BitVec.ofNat 256 (leNat seedBytes)
  let message : Message := BitVec.ofNat 256 (leNat messageBytes)
  let (publicKey, signature) := (do
      let key ← _root_.Sphincs.KeyGenerationAndSigning.expandKey (m := StateM Unit) keccak seed
      let (publicKey, _) ←
        _root_.Sphincs.KeyGenerationAndSigning.keygenInternal (m := StateM Unit) keccak key
      let signature ←
        _root_.Sphincs.KeyGenerationAndSigning.signWithExpandedKey (m := StateM Unit) keccak key
          message
      return (publicKey, signature) : StateM Unit _).run' ()
  let publicKeyOk := hexOf (Sphincs.publicKeyBytes publicKey) == "0x" ++ lines[0]!
  let signatureOk :=
    (signature.map fun s => hexOf (Sphincs.signatureBytes s)) == some ("0x" ++ lines[1]!)
  let verifyOk := signature.map (Sphincs.verify publicKey message) == some true
  IO.println s!"sphincs known_answer: public key {publicKeyOk}, signature {signatureOk}, verify {verifyOk}"
  return publicKeyOk && signatureOk && verifyOk

end SignatureKat

open SignatureKat in
def main (args : List String) : IO UInt32 := do
  let args := args.filter fun arg => !arg.startsWith "--"
  let some (dir : String) := args.head? | do
    IO.eprintln "usage: signature-kat CRATES_DIR [KNOWN_ANSWER_HEX]"
    return 2
  let mut mismatches : UInt32 := 0
  let scheme := "sphincs"
  for kind in ["key_gen", "sign", "verify"] do
    let kindDir : System.FilePath :=
      System.FilePath.mk dir / s!"lean_{scheme}" / "tests" / s!"lean_{scheme}" / "ethlib" / kind
    unless ← kindDir.isDir do continue
    let cases := ((← kindDir.readDir).map (·.path)).qsort (·.toString < ·.toString)
    for case in cases do
      let file := case / "data.yaml"
      unless ← file.pathExists do continue
      let lines := (← IO.FS.readFile file).splitOn "\n"
      let got := runCase scheme kind lines
      let ok := got == expected lines
      IO.println s!"{scheme} {kind} {case.fileName.getD ""}: {if ok then "ok" else "MISMATCH"}"
      unless ok do
        mismatches := mismatches + 1
        IO.println s!"  expected {expected lines}\n  got      {got}"
      (← IO.getStdout).flush
  if let some (hex : String) := args[1]? then
    unless ← knownAnswer (System.FilePath.mk hex) do mismatches := mismatches + 1
  IO.println s!"{mismatches} mismatches"
  return mismatches
