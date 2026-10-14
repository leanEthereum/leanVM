import LeanSphincs.Fts
import LeanSphincs.Ots

/-!
# `LeanSphincs.Verify`

`Ver` (`programs/leansphincs/guest/src/lib.rs` lines 229 to 258 and 289 to 317): 497 hash calls.
-/

namespace LeanSphincs

open LeanSphincs.Constants
open EthCryptographySpecs.Xmss (packBytes)

/-- A byte string read as a little-endian number. -/
def littleEndian (bytes : List UInt8) : Nat :=
  bytes.foldr (fun b acc => b.toNat + 256 * acc) 0

/-- The message digest, read as the index and the `k` few-time leaf indices (`message_digest`, lib.rs lines 289 to
317).

BLAKE2s of the 96 bytes `tweak .msg 0 0 0 0 | P | randomizer | root | message`, all 32 bytes kept. Read
little-endian, its bits `0 .. 25` are the index and bits `26 + 10 kappa .. 35 + 10 kappa` leaf index `kappa`. -/
def messageDigest (pp : PublicParam) (root : Digest) (randomizer : Randomizer) (message : Message) :
    Nat × Vector Nat K :=
  let d := EthCryptographySpecs.Xmss.Blake2s.hash
    (packBytes (tweak .msg 0 0 0 0) ++ packBytes pp ++ packBytes randomizer ++ packBytes root ++ packBytes message)
  let bits := fun offset len => littleEndian d.toList / 2 ^ offset % 2 ^ len
  (bits 0 H, Vector.ofFn fun kappa => bits (H + kappa.val * A) A)

/-- The root layer `lay`'s tree reaches from the message it signs, or nothing if the layer's counter gives that
message no codeword: one step of `verify`'s loop (lib.rs lines 245 to 252). -/
def layerRoot (pp : PublicParam) (idx : Nat) (sig : Signature) (message : Digest) (lay : Fin D) : Option Digest :=
  let pos := Pos.of idx lay
  let (counter, ots, path) := sig.layer lay
  (Ots.leaf pp pos message counter ots).map fun leaf => fold pp .node lay pos.tau pos.e.toNat leaf path

/-- Whether a signature signs a message under a public key (`verify`, lib.rs lines 229 to 258).

* The message digest's last leaf index is zero (FORS+C).
* The few-time key the opening reaches is the message the bottom layer signs, and each layer's root the message of
  the layer above, layers 2, 1, 0 in turn, each counter giving its message a codeword.
* The top layer's root is the key's.

A yes or a no: the guest's three errors carry no meaning past rejection. -/
def verify (pk : PublicKey) (msg : Message) (sig : Signature) : Bool :=
  let pp := pk.publicParam
  let (idx, u) := messageDigest pp pk.root sig.randomizer msg
  if u[K - 1]'(by decide) != 0 then false
  else
    let fts := Fts.recover pp idx u sig.fts
    match [2, 1, 0].foldlM (layerRoot pp idx sig) fts with
    | none => false
    | some top => top == pk.root

end LeanSphincs
