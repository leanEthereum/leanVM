import Statement.LeanSphincs
import Statement.LeanXmss
import Statement.Fast.Schemes
import Statement.Fast.Keccak
import LeanVM.Cli.Common

/-!
# `scheme-vectors`: EthLib's test vectors on the statement's signature schemes, compiled

`lake exe scheme-vectors` runs the statement's leanSPHINCS and leanXMSS
(`Statement/LeanSphincs.lean`, `Statement/LeanXmss.lean`, over Keccak-f[1600] in `Id`) on their
EthLib test vectors as leanVM vendors them (`crates/signatures/tests/signatures/ethlib/{sphincs,xmss}` of
this repository, `../..`; the first argument overrides the directory)
and on leanSPHINCS's known answer (`crates/signatures/src/lean_sphincs/known_answer.hex`, three
directories above it):

* by default, leanSPHINCS's and leanXMSS's verification (`verify`), leanXMSS's signature's leaf
  index (`signature_index`), and the verification of leanSPHINCS's known answer, which must accept,
  and of the same signature with one byte flipped, which must reject;
* with `--xmss-sign`, leanXMSS's key generation and signing (`key_gen`, `sign`): slow (the
  statement's hashes go through its byte and bit-vector conversions, and a key builds a tree of
  `2^16` one-time keys), so run by hand.

leanSPHINCS's key generation and signing (its EthLib `key_gen` and `sign` cases, and the known
answer) are `lean_sphincs`'s `signature-kat`, which compiles the statement's signer with the
`@[csimp]` restatements it needs.

A case whose output is `null` is an input the crate rejects for its length: the statement's
schemes take values of fixed sizes, so it is skipped. The exit code is `0` when every case passes.
Not a proof: evidence that the statement's schemes are the crate's.
-/

open HashSig LeanVM.Cli

namespace SchemeVectors

/-- The bytes of a hexadecimal string, `0x` first. -/
def hexBytes (s : String) : List Nat :=
  let rec go : List Char → List Nat
    | a :: b :: rest => (16 * (hexDigit? a).getD 0 + (hexDigit? b).getD 0) :: go rest
    | _ => []
  go ((s.drop 2).toString.toList)

/-- The 16 bytes at offset `o`. -/
def digestAt (bytes : List Nat) (o : Nat) : Digest := bitsLE 128 ((bytes.drop o).take 16)

/-- A field of a case's YAML: `key: value`, the quotes dropped. -/
def field (text : String) (key : String) : Option String :=
  (text.splitOn "\n").findSome? fun line =>
    let t := line.trimAscii.toString
    if t.startsWith (key ++ ": ") then
      some (((t.drop (key.length + 2)).toString.replace "'" "").replace "\"" "")
    else none

/-- A leanXMSS public key: the root, then the parameter. -/
def publicKeyOf (bytes : List Nat) : PublicKey := ⟨digestAt bytes 0, digestAt bytes 16⟩

/-- A leanSPHINCS public key: `PK.seed`, then `PK.root` (`from_bytes`,
`lean_sphincs/scheme.rs:36-41`). -/
def sphincsPublicKeyOf (bytes : List Nat) : Sphincs.PublicKey :=
  ⟨digestAt bytes 0, digestAt bytes 16⟩

/-- A leanSPHINCS signature (`from_bytes`, `lean_sphincs/scheme.rs:146-173`): the randomizer, 24
FORS openings of a secret and 10 path nodes, then the bottom, middle and top layers, each a 4-byte
big-endian counter, 64 chain values and its tree's siblings. -/
def sphincsSignatureOf (bytes : List Nat) : Sphincs.Signature :=
  let layerStart (layer : Sphincs.Layer) : Nat := 16 + 24 * 176 + 1156 * layer.val
  ⟨digestAt bytes 0,
    fun tree => ⟨digestAt bytes (16 + 176 * tree.val),
      fun level => digestAt bytes (16 + 176 * tree.val + 16 + 16 * level.val)⟩,
    fun layer => ⟨bitsLE 32 ((bytes.drop (layerStart layer)).take 4).reverse,
      fun chain => digestAt bytes (layerStart layer + 4 + 16 * chain.val),
      fun level => digestAt bytes (layerStart layer + 4 + 1024 + 16 * level.val)⟩⟩

/-- A leanXMSS signature (`sign/format.md`): the 4-byte leaf index, then the bottom and top
layers, each a randomizer, 58 chain values and 16 siblings. -/
def xmssSignatureOf (bytes : List Nat) : LeanXmss.Signature :=
  let layerStart (layer : LeanXmss.Layer) : Nat := 4 + 1200 * layer.val
  ⟨(bitsLE 32 (bytes.take 4)).toFin,
    fun layer => ⟨digestAt bytes (layerStart layer),
      fun chain => digestAt bytes (layerStart layer + 16 + 16 * chain.val),
      fun level => digestAt bytes (layerStart layer + 16 + 928 + 16 * level.val)⟩⟩

/-- A case's verdict. -/
inductive Verdict where
  | pass | fail | skip

/-- Runs one case of a kind on its YAML. -/
def runCase (kind : String) (text : String) : Verdict := Id.run do
  let some output := field text "output" | return .fail
  if output == "null" then return .skip
  let bytes (key : String) : List Nat := hexBytes ((field text key).getD "")
  match kind with
  | "xmss/key_gen" =>
    let key := (Id.run (LeanXmss.KeyGenerationAndSigning.keygenFromSeed (m := Id)
      LeanVM.Semantics.keccakF1600 (bitsLE 256 (bytes "seed")))).1
    return if key == publicKeyOf (hexBytes output) then .pass else .fail
  | "xmss/sign" =>
    let (_, secretKey) := Id.run (LeanXmss.KeyGenerationAndSigning.keygenFromSeed (m := Id)
      LeanVM.Semantics.keccakF1600 (bitsLE 256 (bytes "seed")))
    let index := (field text "leaf_index").bind String.toNat? |>.getD 0
    let signature := Id.run (LeanXmss.KeyGenerationAndSigning.sign (m := Id)
      LeanVM.Semantics.keccakF1600 secretKey (BitVec.ofNat 32 index).toFin
      (bitsLE 256 (bytes "message")))
    return if signature == some (xmssSignatureOf (hexBytes output)) then .pass else .fail
  | "xmss/verify" =>
    let ok := LeanXmss.verifyWithKeccak (publicKeyOf (bytes "public_key"))
      (bitsLE 256 (bytes "message")) (xmssSignatureOf (bytes "signature"))
    return if ok == (output == "true") then .pass else .fail
  | "sphincs/verify" =>
    let ok := Sphincs.verifyWithKeccak (sphincsPublicKeyOf (bytes "public_key"))
      (bitsLE 256 (bytes "message")) (sphincsSignatureOf (bytes "signature"))
    return if ok == (output == "true") then .pass else .fail
  | "xmss/signature_index" =>
    let sig := bytes "signature"
    if sig.length != 2404 then return .skip
    return if (xmssSignatureOf sig).leafIndex.val == output.toNat?.getD 0 then .pass else .fail
  | _ => return .fail

/-- The known answer's message `m[i] = 7 i + 3` (`known_answer`, `lean_sphincs/scheme.rs:370-390`;
its key's `SK.seed[i] = 37 i + 11`), from the file's line count, so that the compiler does not
evaluate it as a closed term at start-up. -/
def knownAnswerMessage (lineCount : Nat) : BitVec 256 :=
  let b := if lineCount = 2 then 7 else 0
  bitsLE 256 ((List.range 32).map fun i => (b * i + 3) % 256)

/-- leanSPHINCS's known answer, its two lines the public key's and the signature's hex: its
verification, which must accept, and the signature with its last byte flipped, which must
reject. -/
def knownAnswerCases (lines : List String) : List (String × Verdict) :=
  let message := knownAnswerMessage lines.length
  let publicKeyBytes := hexBytes ("0x" ++ lines.getD 0 "")
  let signatureBytes := hexBytes ("0x" ++ lines.getD 1 "")
  let publicKey := sphincsPublicKeyOf publicKeyBytes
  let signature := sphincsSignatureOf signatureBytes
  let flipped := sphincsSignatureOf
    (signatureBytes.dropLast ++ [(signatureBytes.getLastD 0) ^^^ 1])
  let verdict (ok : Bool) : Verdict := if ok then .pass else .fail
  [("verify", verdict (signatureBytes.length == 7740 &&
      Sphincs.verifyWithKeccak publicKey message signature)),
    ("verify, a byte flipped", verdict !(Sphincs.verifyWithKeccak publicKey message flipped))]

end SchemeVectors

open SchemeVectors in
/-- The driver: every case of every kind, in order. -/
def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := (args.filter (!·.startsWith "--")).headD
    "../../crates/signatures/tests/signatures/ethlib"
  let kinds := ["sphincs/verify", "xmss/verify", "xmss/signature_index"] ++
    (if args.contains "--xmss-sign" then ["xmss/key_gen", "xmss/sign"] else [])
  let mut failed := 0
  let mut passed := 0
  let mut skipped := 0
  let knownAnswer := root / ".." / ".." / ".." / "src" / "lean_sphincs" / "known_answer.hex"
  let lines := (← IO.FS.readFile knownAnswer).splitOn "\n" |>.filter (· ≠ "")
  for (name, verdict) in knownAnswerCases lines do
    match verdict with
    | .pass => passed := passed + 1; IO.println s!"sphincs/known_answer {name}: ok"
    | .skip => skipped := skipped + 1
    | .fail => failed := failed + 1; IO.println s!"sphincs/known_answer {name}: FAILED"
    (← IO.getStdout).flush
  for kind in kinds do
    let dir := root / kind
    let entries ← dir.readDir
    let cases := (entries.map (·.fileName)).qsort (· < ·)
    for name in cases do
      let file := dir / name / "data.yaml"
      unless ← file.pathExists do continue
      let text ← IO.FS.readFile file
      let start ← IO.monoMsNow
      let verdict := runCase kind text
      let ms := (← IO.monoMsNow) - start
      match verdict with
      | .pass => passed := passed + 1; IO.println s!"{kind}/{name}: ok ({ms} ms)"
      | .skip => skipped := skipped + 1; IO.println s!"{kind}/{name}: skipped (an input of another length)"
      | .fail => failed := failed + 1; IO.println s!"{kind}/{name}: FAILED"
      (← IO.getStdout).flush
  IO.println s!"{passed} passed, {failed} failed, {skipped} skipped"
  return if failed == 0 && passed > 0 then 0 else 1
