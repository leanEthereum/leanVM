import Statement.Prover.Run
import Statement.Fast.Keccak
import LeanVM.Prover.Fast.Sponge

/-!
# Transcript tests: packed messages and packed draws

The sponge's packed operations (`observePacked`, `samplesPacked`, `Statement/Field.lean`), the
verifier's packed reads and draws (`VerifierProgram.readPacked`, `samplePacked` and their `run`
cases, `Statement/Verifier/Transcript.lean`) and the prover's packed moves (`Script.sendPacked`,
`Script.samplePacked` and their `runFrom` cases, `Statement/Prover/`) against the Rust
(`Sponge::observe_packed`, `Sponge::samples_packed`, `Transcript::next_scalars_packed`,
`crates/verifier/src/transcript.rs`; `FiatShamirState::observe_packed`, `sample_packed`,
`ProverState::add_scalars_packed`, `crates/fiat_shamir_prover`).

A case is a schedule of moves from the sponge seeded with the IV words `1, 2, 3, 4` and the public
input words `5, 6, 7, 8`: sends of `n` scalars, one at a time or packed, scalar `j` of the
schedule being `E(j + 1, (j + 1)·2^32 + 0x5eed)`; draws of one challenge or `n` packed; grinds.
The Rust prover ran each schedule (`ProverState`, grinding with `Sequential`) and the Rust
verifier read its proof back (`Transcript`, checked); the expected values are the nonces the
prover found and Keccak-256 of the challenges' bytes (`E::to_bytes`, both limbs little-endian),
at the branch `hotwire` (a scratch test in `crates/fiat_shamir_prover/tests/`, not committed).
The cases:

* a packed message of each length `0..=20` after `0`, `1` or `4` waiting scalars, then one
  challenge: the permutation of the waiting scalars, whole and partial chunks of eight, the rate
  zero past the message;
* a packed draw of each count `0..=20` from a fresh sponge, after a waiting scalar, and after a
  grind of `1` and of `6` bits, then one challenge: the grind's permutation giving the ground
  challenge and its cells `2..8`, the proof-of-work cell skipped, then whole permutations;
* four mixed schedules.

For each, Lean's verifier reads the stream (the scalars sent and the nonces) and draws the same
challenges, consuming the stream; Lean's prover writes the same stream, its nonces the smallest
passing ones as the Rust's. Then a packed draw of nine after a `6`-bit grind, challenge by
challenge, and the rejections: a packed read while a grind's challenge waits (the Rust's
`observe_packed` asserts) and one past the stream's end (`next_scalars_packed`'s
`StreamExhausted`).
-/

namespace LeanVMTests.Protocol.Transcript

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Prover

/-- A move of a schedule. -/
inductive Op where
  | send (n : ℕ)
  | sendPacked (n : ℕ)
  | sample
  | samplePacked (n : ℕ)
  | grind (bits : ℕ)

/-- Scalar `j` of a schedule. -/
def val (j : ℕ) : E := E.ofLimbs (K.ofBits (j + 1)) (K.ofBits ((j + 1) * 2 ^ 32 + 0x5eed))

/-- The scalars `j, …, j + n - 1` of a schedule. -/
def vals (j n : ℕ) : List E := (List.range n).map (val <| j + ·)

/-- The sponge's seed: the IV words `1, 2, 3, 4` and the public input words `5, 6, 7, 8`. -/
def seed : KeccakState := keccakF1600 (seedInput #v[1, 2, 3, 4] #v[5, 6, 7, 8])

/-- The verifier's program of a schedule: the challenges, in order. -/
def program : List Op → VerifierProgram (List E)
  | [] => pure []
  | .send n :: ops => do
    let _ ← VerifierProgram.readScalars n
    program ops
  | .sendPacked n :: ops => do
    let _ ← VerifierProgram.readScalarsPacked n
    program ops
  | .sample :: ops => do
    let c ← VerifierProgram.sampleChallenge
    let cs ← program ops
    pure (c :: cs)
  | .samplePacked n :: ops => do
    let c ← VerifierProgram.sampleChallengesPacked n
    let cs ← program ops
    pure (c ++ cs)
  | .grind bits :: ops => do
    VerifierProgram.grindProofOfWork bits
    program ops

/-- The prover's script of a schedule, from scalar `j`. -/
def script : List Op → ℕ → Script Unit
  | [], _ => pure ()
  | .send n :: ops, j => do
    Script.sendList (vals j n)
    script ops (j + n)
  | .sendPacked n :: ops, j => do
    Script.sendPackedS (vals j n)
    script ops (j + n)
  | .sample :: ops, j => do
    let _ ← Script.sampleE
    script ops j
  | .samplePacked n :: ops, j => do
    let _ ← Script.samplePackedS n
    script ops j
  | .grind bits :: ops, j => do
    Script.grindBits bits
    script ops j

/-- A schedule's stream from scalar `j`, with the nonces of its grinds of nonzero bits. -/
def stream : List Op → ℕ → List ℕ → List E
  | [], _, _ => []
  | .send n :: ops, j, ns | .sendPacked n :: ops, j, ns => vals j n ++ stream ops (j + n) ns
  | .grind bits :: ops, j, ns =>
    if bits = 0 then stream ops j ns else nonceOf (ns.headD 0) :: stream ops j ns.tail
  | _ :: ops, j, ns => stream ops j ns

/-- Lean's verifier on a schedule's stream: the challenges, if it reads the stream whole. -/
def verifierChallenges (ops : List Op) (nonces : List ℕ) : Option (List E) :=
  match Id.run (run (m := Id) keccakF1600 (program ops)
      ⟨⟨seed, [], none⟩, stream ops 0 nonces, [], []⟩) with
  | some (cs, s) => if s.stream.isEmpty then some cs else none
  | none => none

/-- Lean's prover on a schedule: the stream, its nonces searched below `2^12`. -/
def proverStream (ops : List Op) : Option (List E × List (List Opening)) :=
  Id.run (runFrom (m := Id) keccakF1600 (2 ^ 12) (program ops) (some (script ops 0))
    ⟨seed, [], none⟩ [])

/-- A case: the schedule, the Rust's nonces, the number of challenges and their digest. -/
structure Case where
  ops : List Op
  nonces : List ℕ
  count : ℕ
  digest : Digest

/-- Lean's verifier draws the Rust's challenges, and Lean's prover writes the Rust's stream. -/
def Case.holds (c : Case) : Bool :=
  (match verifierChallenges c.ops c.nonces with
    | some cs => cs.length == c.count && keccak256 (cs.flatMap E.toBytes) == c.digest
    | none => false) &&
  match proverStream c.ops with
  | some (s, []) => s == stream c.ops 0 c.nonces
  | _ => false

/-- The Rust's cases (`print_lean_vectors`). -/
def cases : List Case := [
  ⟨[.sendPacked 0, .sample],
    [], 1, #v[0x17e28495576bf1e3, 0xae9c595bae932ec6, 0x258c8054f3f79155, 0x58f79b2ee88e902b]⟩,
  ⟨[.sendPacked 1, .sample],
    [], 1, #v[0x776c97ac12c8e2f9, 0x973fca3397ce8c02, 0xe870a1b80d6446b8, 0x7ae5600a7470cd0d]⟩,
  ⟨[.sendPacked 2, .sample],
    [], 1, #v[0x6f9417eeeb5fc31c, 0x658cf875f5da92d9, 0xf09405103c2ffca5, 0x210dd199b26fe3a3]⟩,
  ⟨[.sendPacked 3, .sample],
    [], 1, #v[0x517b9abdb4adeb7f, 0x483c1bfb76a2cc3d, 0x6781754981fdc0db, 0x7762c9567a6d8e97]⟩,
  ⟨[.sendPacked 4, .sample],
    [], 1, #v[0xd0e8b239dbb61ad7, 0x5f1bb7b654056ec3, 0x8be3b987ce74b192, 0x6f18b92a89957fe3]⟩,
  ⟨[.sendPacked 5, .sample],
    [], 1, #v[0x8dffa51a452e00ba, 0x814193c26904a5b1, 0xfbcc4e2c15e14b63, 0x690312caf59ec92d]⟩,
  ⟨[.sendPacked 6, .sample],
    [], 1, #v[0xdf2e81aee9e80722, 0xb7be1a931d0bbb2b, 0x91e6fc5729e66b3f, 0xd9b0624e2f7d8342]⟩,
  ⟨[.sendPacked 7, .sample],
    [], 1, #v[0xd34a8378777f6542, 0x5e0f70962fd776ed, 0xfbad7525d5c60549, 0x97a88f06646a110f]⟩,
  ⟨[.sendPacked 8, .sample],
    [], 1, #v[0xc3b5cc5b4ffb2eca, 0xfb14ccc9a3bcfe90, 0x63e6c3ea561b2b29, 0x1143c53c9dbb4d05]⟩,
  ⟨[.sendPacked 9, .sample],
    [], 1, #v[0xdb8da6e947af6dd5, 0xd0c09af467d91666, 0xdd09b75a857cf709, 0xfb2a4e9a19421ba]⟩,
  ⟨[.sendPacked 10, .sample],
    [], 1, #v[0xbceaefc42888f88e, 0x20de9bdf72fa6502, 0xfdae37636276323a, 0x8922ee0ed816c092]⟩,
  ⟨[.sendPacked 11, .sample],
    [], 1, #v[0xc0ce9620e69ff48a, 0xe87f9ca3de43c40b, 0x3fbecd972ab6db3c, 0xfef45d960704bb12]⟩,
  ⟨[.sendPacked 12, .sample],
    [], 1, #v[0xb607168cceae67d7, 0x6d7967b1ccfada9e, 0x54de7cac21715fa5, 0x9bd24ee3c562fa16]⟩,
  ⟨[.sendPacked 13, .sample],
    [], 1, #v[0x6894d0e90861569e, 0xf64cf4ca5e6f98fd, 0xec24383182f9a196, 0x5f121168e5895b20]⟩,
  ⟨[.sendPacked 14, .sample],
    [], 1, #v[0x5e6487aa71a6a739, 0x97fe0bdec2a2f617, 0xbb02ba5d79f06e19, 0xf2c20f450257087c]⟩,
  ⟨[.sendPacked 15, .sample],
    [], 1, #v[0x49bf3c8dfe2c83a8, 0x4bcdade5bff13221, 0xd98a289ceb0865ec, 0x69b48e67bab33514]⟩,
  ⟨[.sendPacked 16, .sample],
    [], 1, #v[0x10fcb11fadddab04, 0x7b94c3a1f67ed3e9, 0x769f2ff626a36c0a, 0xa207f29f6293d991]⟩,
  ⟨[.sendPacked 17, .sample],
    [], 1, #v[0x20ecd86a6238a6b9, 0x2d925e48d0e381f5, 0xfa963fbeabd4104c, 0x46e98ca53933250c]⟩,
  ⟨[.sendPacked 18, .sample],
    [], 1, #v[0xcfda85056576dd8, 0x981933cbdb4f825e, 0xae2ca9e306ed95d3, 0x24b38d0ca95be83]⟩,
  ⟨[.sendPacked 19, .sample],
    [], 1, #v[0x44c5851ce4cfce99, 0x39512b54d1cce935, 0xec8d449e4947cdba, 0xa1cb797b103a5e84]⟩,
  ⟨[.sendPacked 20, .sample],
    [], 1, #v[0x9dd45ae6db30c483, 0x819488e79c62f225, 0x3dce83cc3c97fc3f, 0x63007c79ed7d537a]⟩,
  ⟨[.send 1, .sendPacked 0, .sample],
    [], 1, #v[0xff331f2a020d5784, 0xb6a3e1b3e6cf2668, 0x81a18a2d2ccd899e, 0x54bcdcb6a486061d]⟩,
  ⟨[.send 1, .sendPacked 1, .sample],
    [], 1, #v[0x8e175b53bde1b0db, 0x4ddab209a1f898d3, 0x126634bd65b7eb21, 0xc12d34e2f946cba2]⟩,
  ⟨[.send 1, .sendPacked 2, .sample],
    [], 1, #v[0x93585516dadb3c59, 0x26cfa82a1ff996cf, 0xad1385d4b4972f03, 0xcd00b933b09fa8a1]⟩,
  ⟨[.send 1, .sendPacked 3, .sample],
    [], 1, #v[0x18591041ca3d39f3, 0xc841c045b3025451, 0x74a0baf3682d61d4, 0x5c189b3f6eb579b7]⟩,
  ⟨[.send 1, .sendPacked 4, .sample],
    [], 1, #v[0x61d1b17dd06e867e, 0x50d706034d15d577, 0x4132ec3891e0327d, 0x83ba4539c6d7ff31]⟩,
  ⟨[.send 1, .sendPacked 5, .sample],
    [], 1, #v[0x1d50f342e3b07ff2, 0x8e25affc0dad9801, 0xe209d172fd6165fd, 0xcd6dcd390ef08730]⟩,
  ⟨[.send 1, .sendPacked 6, .sample],
    [], 1, #v[0xfbbe0b529e004a21, 0x8374b8673c34a98f, 0x3cca472e52ac0907, 0xfbfcfee1c832d106]⟩,
  ⟨[.send 1, .sendPacked 7, .sample],
    [], 1, #v[0xb5f1362485fc140e, 0xe8beb9c629265a39, 0x2f98a10d9e07c94a, 0xaef443e68bc2b0eb]⟩,
  ⟨[.send 1, .sendPacked 8, .sample],
    [], 1, #v[0x12084d2ecbba28c6, 0x9b06c92f700e2090, 0xced91e7beeb7b1d, 0xbda65d5c1c2e163a]⟩,
  ⟨[.send 1, .sendPacked 9, .sample],
    [], 1, #v[0x44f0816583b7ed01, 0x9534298d1898226a, 0x234b48f9fcfb4b6a, 0xf364d1baf389ebcf]⟩,
  ⟨[.send 1, .sendPacked 10, .sample],
    [], 1, #v[0x44de6de49d973389, 0xfcdbaa74ce7ec6e, 0x436336e98cda50bf, 0x96ca3fe8b755da00]⟩,
  ⟨[.send 1, .sendPacked 11, .sample],
    [], 1, #v[0x832ff680e25b7400, 0xb6d04d3582d95da7, 0xe659067fcb8fd891, 0xd7accdaaac852372]⟩,
  ⟨[.send 1, .sendPacked 12, .sample],
    [], 1, #v[0x6b7631541a7af92e, 0x6899a19e04b616c4, 0xba257bf7ac3a9f3b, 0x19fea45fa1d8c793]⟩,
  ⟨[.send 1, .sendPacked 13, .sample],
    [], 1, #v[0x52c48fb438e2afc1, 0x5a403d5466efe50d, 0xd04ee04be3fc7d82, 0x9f49cc0b8708677c]⟩,
  ⟨[.send 1, .sendPacked 14, .sample],
    [], 1, #v[0xcc3bfd8f91ef3d1, 0xde84b8f1f6a42721, 0xa20485bc40e26ba2, 0xe36100a79e10f769]⟩,
  ⟨[.send 1, .sendPacked 15, .sample],
    [], 1, #v[0x9ee16c1d54773362, 0xfa355d645db883bd, 0x3223fc827b4e246e, 0xfb65105fcd1af8c7]⟩,
  ⟨[.send 1, .sendPacked 16, .sample],
    [], 1, #v[0x55d8ce4f1e87b6c1, 0x617c3ce63cddea39, 0xcf25e49b0b00589b, 0x6877354187d9b08f]⟩,
  ⟨[.send 1, .sendPacked 17, .sample],
    [], 1, #v[0x84f401c979200fef, 0x1486d6e73c9a3aec, 0x15c9057242e5979a, 0xf6827f0083470369]⟩,
  ⟨[.send 1, .sendPacked 18, .sample],
    [], 1, #v[0xdf8cf6bb1a3e6f98, 0x7957c4065e8bc514, 0x724c5c9cd453c5c1, 0x3e4cfc1fdf472975]⟩,
  ⟨[.send 1, .sendPacked 19, .sample],
    [], 1, #v[0xde9f6d7909c9f95e, 0xa4183457fb0aef3c, 0x630f198f66e746cc, 0x3601bcb84da47c9d]⟩,
  ⟨[.send 1, .sendPacked 20, .sample],
    [], 1, #v[0x26db3a5ce9f22179, 0xaf37802f99103b0d, 0x6c700357e3916b81, 0xa57c73ceb03e3d27]⟩,
  ⟨[.send 4, .sendPacked 0, .sample],
    [], 1, #v[0x12a39c862ee0cc97, 0x1f8ed933cd1d2b19, 0x841c51c1a4d39423, 0xd93da2ee13e6641]⟩,
  ⟨[.send 4, .sendPacked 1, .sample],
    [], 1, #v[0x2122c0591aa2231f, 0x88d34052da21f7d2, 0x924e293cb92f860c, 0xcfb5fb34dc33ec1b]⟩,
  ⟨[.send 4, .sendPacked 2, .sample],
    [], 1, #v[0xa88b13e8f3c35565, 0x31f299bead839144, 0x16dc7e66d8dd6eb6, 0xf26cb49b74deea11]⟩,
  ⟨[.send 4, .sendPacked 3, .sample],
    [], 1, #v[0x9400255cf086fd1e, 0x6c908fc3a1e6971, 0x9bd69d0996c795af, 0x20ff409b2f4f1f20]⟩,
  ⟨[.send 4, .sendPacked 4, .sample],
    [], 1, #v[0xa4cc3892f8f9535a, 0x6604e4fad3c5f713, 0x5dc4b51fb1b0fa70, 0x3e5369be19d22795]⟩,
  ⟨[.send 4, .sendPacked 5, .sample],
    [], 1, #v[0xef9bd5a816b4d9d, 0xcac4da325abcd0ff, 0x16ce2050b62b8591, 0x492570075d192b38]⟩,
  ⟨[.send 4, .sendPacked 6, .sample],
    [], 1, #v[0xb944afe12b0e5942, 0x7ff0b4c637985356, 0x68c8ed8c04ab2746, 0xc2dacdb998f2382b]⟩,
  ⟨[.send 4, .sendPacked 7, .sample],
    [], 1, #v[0x32ed2e80c2ded01, 0x33b055b9d7336a91, 0xb7d7735f38d83a6, 0xb3e84db945305b77]⟩,
  ⟨[.send 4, .sendPacked 8, .sample],
    [], 1, #v[0x8e818d9db6b09970, 0xe77d88ce129ee893, 0xe72ac3cc91f1da57, 0x21fcac3107aee3d]⟩,
  ⟨[.send 4, .sendPacked 9, .sample],
    [], 1, #v[0xa1ee2e85c2a7bce0, 0x834dfa8145ba2113, 0x1b645a5aa82501ee, 0x341db52a507d35a5]⟩,
  ⟨[.send 4, .sendPacked 10, .sample],
    [], 1, #v[0x90bcff60650477c9, 0x7e3cdfbc55ddb206, 0x12f9f4bf1d78cba7, 0x8b16cb02c8126bd]⟩,
  ⟨[.send 4, .sendPacked 11, .sample],
    [], 1, #v[0x9d0deea7160d765a, 0x60f9b7246ef7b29c, 0xafdce8fd66a500b3, 0x1d54c07290c06577]⟩,
  ⟨[.send 4, .sendPacked 12, .sample],
    [], 1, #v[0x1610ef15efee0663, 0x4f3fa56fc7e632c0, 0x9cb9d6464c79bc78, 0x1b1697d61157ffcf]⟩,
  ⟨[.send 4, .sendPacked 13, .sample],
    [], 1, #v[0x145aa14cfa120604, 0xd347c88c7176e63d, 0xef963ecb292df634, 0x8a93bde6187d7677]⟩,
  ⟨[.send 4, .sendPacked 14, .sample],
    [], 1, #v[0xe483fdc55765209d, 0xd6ea8f4defce947e, 0x8bdba15ec57ac45c, 0x5716502d1d641a47]⟩,
  ⟨[.send 4, .sendPacked 15, .sample],
    [], 1, #v[0xf956e76295d733e5, 0x508dd1a59229dd6a, 0xbd7dd215ef2f0257, 0xed22e0f0d2404981]⟩,
  ⟨[.send 4, .sendPacked 16, .sample],
    [], 1, #v[0x690f3c3688739d8f, 0x1104d0c937bd52e, 0x367415a1d9cab339, 0x1b806fc7073e0710]⟩,
  ⟨[.send 4, .sendPacked 17, .sample],
    [], 1, #v[0xaed3c29a739e92cb, 0x5d14ea43be041469, 0x47f340085858253b, 0x47b2490ad18be718]⟩,
  ⟨[.send 4, .sendPacked 18, .sample],
    [], 1, #v[0xbbf758555b995286, 0xc4d660a2c53f28e3, 0xd899509af53ade57, 0xf0d41ad758b80218]⟩,
  ⟨[.send 4, .sendPacked 19, .sample],
    [], 1, #v[0xe2b467a0ecb65e8, 0x116c64fa7b3093b4, 0x53b89e0ef936cf14, 0xd3930118071f0053]⟩,
  ⟨[.send 4, .sendPacked 20, .sample],
    [], 1, #v[0x4d5506df661d20b1, 0x6279e6afd3dbde18, 0x76099aeb06960429, 0x528eb50eaee3a7f2]⟩,
  ⟨[.grind 0, .samplePacked 0, .sample],
    [], 1, #v[0x17e28495576bf1e3, 0xae9c595bae932ec6, 0x258c8054f3f79155, 0x58f79b2ee88e902b]⟩,
  ⟨[.grind 0, .samplePacked 1, .sample],
    [], 2, #v[0x9af0a29fc3377cce, 0x4370b2bff257fb5b, 0xe2ff65e7824813e, 0x5e8f42dd285e6848]⟩,
  ⟨[.grind 0, .samplePacked 2, .sample],
    [], 3, #v[0xa004fca781840961, 0xdf6a6980b9a98675, 0x807ea54b47f033c0, 0x570e4cd303a318dd]⟩,
  ⟨[.grind 0, .samplePacked 3, .sample],
    [], 4, #v[0x25eece646503dcff, 0x7dd6fc20bb7e3b0b, 0xc07de03908265895, 0xbaba53856b0e51ee]⟩,
  ⟨[.grind 0, .samplePacked 4, .sample],
    [], 5, #v[0xba222e8681b2633b, 0x314529a6a1dc868a, 0xde8ac7a47a03f725, 0x95db1f1fcb4388a2]⟩,
  ⟨[.grind 0, .samplePacked 5, .sample],
    [], 6, #v[0x1336e03318c8e82, 0xb91005edbb2129a1, 0xe486cf92bce0ff4d, 0xf33518829fbc8f8e]⟩,
  ⟨[.grind 0, .samplePacked 6, .sample],
    [], 7, #v[0x8d94d920e06d8775, 0x2116b69a908f8687, 0x421ebd2d9c55b29f, 0x8282b7c5b8213891]⟩,
  ⟨[.grind 0, .samplePacked 7, .sample],
    [], 8, #v[0x4603fb5e5cb04f74, 0xe8d9278715fda27c, 0xff10e879515f70bd, 0xc14b16ce64bcee0d]⟩,
  ⟨[.grind 0, .samplePacked 8, .sample],
    [], 9, #v[0x2f71eb2d0b2988bd, 0x962762ff4305dcc8, 0x6d1250766a224568, 0x34eb0ee7f1132eac]⟩,
  ⟨[.grind 0, .samplePacked 9, .sample],
    [], 10, #v[0xa3a6222dfcdd4178, 0x2bf9e51386319106, 0x8fef8166be962ff, 0x3555a99799920e67]⟩,
  ⟨[.grind 0, .samplePacked 10, .sample],
    [], 11, #v[0x9423b6841638e391, 0x46c21b56e21ca179, 0x3d70f946cc28f621, 0xf90893a6df9dac38]⟩,
  ⟨[.grind 0, .samplePacked 11, .sample],
    [], 12, #v[0x389b00c859cee6f, 0x343b7c66fc30a135, 0x1330eba5f62df666, 0x36a598386f20e859]⟩,
  ⟨[.grind 0, .samplePacked 12, .sample],
    [], 13, #v[0x33c5a4ef56c21367, 0x838280443fd7c0c9, 0x1eab849bb71bf7d6, 0x9adc77497dec2506]⟩,
  ⟨[.grind 0, .samplePacked 13, .sample],
    [], 14, #v[0x74728f94e5ce68ef, 0xd179b264811dce78, 0x9bc94fd17714b39a, 0x41315f84f5db795a]⟩,
  ⟨[.grind 0, .samplePacked 14, .sample],
    [], 15, #v[0xa067becd32f63adf, 0x9d7290aaf47f2cc5, 0xa593ae50049f518b, 0x4387565d4d8bf9e8]⟩,
  ⟨[.grind 0, .samplePacked 15, .sample],
    [], 16, #v[0xcf60a75288d9229, 0xe49921b3c4069d87, 0x3d330e1834f407e2, 0xabb4f0d3a2ac71bf]⟩,
  ⟨[.grind 0, .samplePacked 16, .sample],
    [], 17, #v[0x36cdd6fe478e8bd7, 0xae3c950cc71318cc, 0x95e82b1e1daeb8bb, 0x7770952de9be763f]⟩,
  ⟨[.grind 0, .samplePacked 17, .sample],
    [], 18, #v[0x9640ebe8e2e31945, 0x2e0a0a0f48933f35, 0xcae475973a31ce8a, 0xe194700d0e6e2109]⟩,
  ⟨[.grind 0, .samplePacked 18, .sample],
    [], 19, #v[0x2ecb44c4d7f5de46, 0x67d3ce1198980152, 0xa6ea54e4b30155, 0xc136610a91423261]⟩,
  ⟨[.grind 0, .samplePacked 19, .sample],
    [], 20, #v[0x3bdbfb2f9a160324, 0xa10303cb04e6af9, 0xfacfc0c26e435868, 0x2a29335a398a0082]⟩,
  ⟨[.grind 0, .samplePacked 20, .sample],
    [], 21, #v[0xd450be74f9467661, 0x3fe73fec9dca126, 0xa0be04b1a715e33b, 0x613286ed0b490245]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 0, .sample],
    [], 1, #v[0xb117c38b231c81c8, 0x24c5588dec77b431, 0x346bec1b8936499e, 0x4dea0871ead8cb70]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 1, .sample],
    [], 2, #v[0xafecadf558ccba37, 0xaf9fd05f05cca60c, 0xc56421de07236e58, 0xedfcd3eca1568f48]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 2, .sample],
    [], 3, #v[0x36445a139cd439c5, 0x9b9193cefa5364, 0x4045c2498f054b20, 0xfd4dac600abf161c]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 3, .sample],
    [], 4, #v[0xaf683259da47e5b5, 0x6b22e65e3443bea3, 0xc10c669906fc3fe2, 0x7f6c8b78edce373b]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 4, .sample],
    [], 5, #v[0xa97195dd1cf79900, 0xdbc80d62e06c48cb, 0x652a400d8bb96739, 0xc9c3e5a5a2d26a04]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 5, .sample],
    [], 6, #v[0x996e68033714f0ba, 0x2786119d4da2cc58, 0x909c3b62182d3194, 0x6f4e1c80f2d2de44]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 6, .sample],
    [], 7, #v[0x464a2f5b9ee939a8, 0x74501dde6ff3efc7, 0x80dd557b31fb3e37, 0x86b5aeb429e7635f]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 7, .sample],
    [], 8, #v[0x8b06971d05498ce3, 0xb90e8edb4b76809a, 0x33117e3c23233187, 0xc14b3e80180fa7c9]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 8, .sample],
    [], 9, #v[0xa6a0745f64156f92, 0x384fb64c7fe2d1b2, 0xe49d163860d103a7, 0xe92c24436f860dbc]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 9, .sample],
    [], 10, #v[0x55d5ffca765efab1, 0x1b460bddf4af4d01, 0xcedd6783714bbb21, 0xdeff2ab9c4e3eaa9]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 10, .sample],
    [], 11, #v[0xb6b75e8850db85aa, 0x14adaa662531849f, 0x832c4010d58b25c3, 0x725c5585c131f91c]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 11, .sample],
    [], 12, #v[0xf47ed2619fde39dd, 0x646c51ab74c63d48, 0xb9e4853789f5f65e, 0x6527e567bff75d98]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 12, .sample],
    [], 13, #v[0x8a9e85e8f1e3fe6e, 0x368f1e6c892fe655, 0x6b1bc1a3bd78122a, 0x18cd2ef2198eb507]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 13, .sample],
    [], 14, #v[0x95e267a4198732ec, 0x492a4a778cf61c9b, 0x5309e69ff78ee464, 0xf8e9ce006137bf66]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 14, .sample],
    [], 15, #v[0xa0c448051824278a, 0xf73c5f6efb046977, 0xdb9bee6c7380e271, 0x3abe0827fea30978]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 15, .sample],
    [], 16, #v[0xdbc91753b7cbc8de, 0x364c957954856f19, 0x8b05115f13f3e19, 0x81109eab182893e3]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 16, .sample],
    [], 17, #v[0x45aed7510039712c, 0xdbf0e7cdb6c668db, 0x453cc8013c478c90, 0x8a7e3b68780882da]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 17, .sample],
    [], 18, #v[0xeeba9f9dc0e3687f, 0x993882fdf8f03941, 0xa019b5d94b1929c2, 0xead3a9c5b0b03bec]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 18, .sample],
    [], 19, #v[0x5327cc099889aa38, 0xe5e95b6391cef73, 0x4822fbe986d83813, 0x9daeabeaf1fc0799]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 19, .sample],
    [], 20, #v[0x2064f00c8c9ad2ac, 0x175e73f462f87b0a, 0x902ee35478106ed3, 0xf05eb7ad78d10637]⟩,
  ⟨[.send 1, .grind 0, .samplePacked 20, .sample],
    [], 21, #v[0xb41e5b4167fa3a4f, 0x98428d3eff74c960, 0x8c9415eb4d7d8016, 0x1da2b7c24c350639]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 0, .sample],
    [0], 1, #v[0xe41cfc21fcdcbf4a, 0x1e64e5dce09a7366, 0x2cd472067ba1a176, 0x4bba287d98eed73]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 1, .sample],
    [0], 2, #v[0xe2a14a2bde968725, 0xc15efdc12128c231, 0x1eaa56e32d3e591c, 0xb3d142f0ec2e6af0]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 2, .sample],
    [0], 3, #v[0x8217f14d51cc44a6, 0xb6b9bd7e7bea98f7, 0xb709511111155a8e, 0xe5f686b22b41186c]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 3, .sample],
    [0], 4, #v[0xf1c04a70903adf6f, 0xd9d3bd19360d5684, 0x345eca683e074d74, 0x41ef8c5b4244aa3b]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 4, .sample],
    [0], 5, #v[0xe93e14423e360720, 0xd64f3b7c6816c056, 0xc980e9e2f5cb5933, 0x23e257c86818cbd3]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 5, .sample],
    [0], 6, #v[0x5c075006c529136, 0xd1597049a83bc841, 0x156e190556aa5ca4, 0xf2fcf95fac60adf6]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 6, .sample],
    [0], 7, #v[0xa9a24f98ac217b42, 0x80f15c7fd1c1ddd8, 0xa5b470bdb169a3cc, 0x94f2e064ebef6aed]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 7, .sample],
    [0], 8, #v[0x56fffee116b7bcb8, 0xc8e073edf163964e, 0x7849ff39e63ca1d4, 0x619cfc01990646a0]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 8, .sample],
    [0], 9, #v[0xcf84048c44a47435, 0xe035755a81dfc867, 0x33aec3f8ee9392e5, 0xea17e07af639580f]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 9, .sample],
    [0], 10, #v[0x23911e26f2ee5065, 0x2e57a72f0d158249, 0x3ab8f9c7c84eeb6d, 0xd0fdd9b5efd64c1d]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 10, .sample],
    [0], 11, #v[0x9e49fb73dd49e964, 0x71c79b5021e5a93d, 0xd1c854af1dcc9098, 0xff0962298860b956]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 11, .sample],
    [0], 12, #v[0xa4a2472ef006c8c9, 0x4b8a3f3b2408770b, 0xe4c8fea4a2f12ff5, 0x626524292179b213]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 12, .sample],
    [0], 13, #v[0xf61a2cea240008b7, 0x23209c38b3a2ac66, 0x40060291b0ef0810, 0x86904ed1b4092f3e]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 13, .sample],
    [0], 14, #v[0xa6c15fa6f88304c5, 0x5269c7bdb7e48b81, 0x479685503a812029, 0x24a3dc25490fb43d]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 14, .sample],
    [0], 15, #v[0xa8e7098cdde1c3de, 0x67c931da81d5d6a3, 0xf16a40a2cc356b1e, 0xbe5463ee90b36df6]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 15, .sample],
    [0], 16, #v[0x3fdc28e8c51f218c, 0x6626aadfc4ee0861, 0xac825113dab1f637, 0x4a5084d07ffb83f]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 16, .sample],
    [0], 17, #v[0x5bda0dc896db99fb, 0x2a194172603bb208, 0xd0550975bf3f0785, 0x83ab13b18918662e]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 17, .sample],
    [0], 18, #v[0xf8b7a3f97fa28357, 0x2410ad4781ad2dbd, 0xfcd4783bdead55f2, 0xf966f78c5b5df656]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 18, .sample],
    [0], 19, #v[0x1c56d6020ee234aa, 0x96c5adfeb850b5b0, 0xfdc0f6ca41564de7, 0x85220e93442782eb]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 19, .sample],
    [0], 20, #v[0xaa31db79379b1782, 0x5ecc241809d73be4, 0x8763a48e01a17c08, 0xfa6f10cf4787ab2f]⟩,
  ⟨[.send 1, .grind 1, .samplePacked 20, .sample],
    [0], 21, #v[0xeef581d34903fb0e, 0x291a224299264665, 0xf4e133f52e877139, 0x38b335d16bbdb7b5]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 0, .sample],
    [43], 1, #v[0xc87699b669f977ac, 0x571f8e149c7ed2f, 0xcf99306089722c8e, 0x8abbe18e545c5913]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 1, .sample],
    [43], 2, #v[0xb0d9a66385fa1ccf, 0xec1ccabd43f647f7, 0x73dfa225159c7bd4, 0x187f81408cf99672]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 2, .sample],
    [43], 3, #v[0x9db706f2568f0764, 0x3107e82101b854c4, 0xdd202679a746d03, 0x381f9e16596ebfa4]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 3, .sample],
    [43], 4, #v[0x97b5d836776a29aa, 0x1fd10d522b82ba4b, 0x234ecf6a6ea85881, 0xb556520f21f6ca66]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 4, .sample],
    [43], 5, #v[0x99c5333a5cd1a780, 0xe5e2d2dd44a2f89b, 0x92d703f37accb690, 0xc10cc45d97334093]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 5, .sample],
    [43], 6, #v[0xcee3c1871dba0899, 0xdb967b2a41740eb8, 0x10e15827154b61a0, 0xf2b860044bf7c2b4]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 6, .sample],
    [43], 7, #v[0x3e534609d2151015, 0x33fa6e698b1e64c0, 0x90c803fc20275821, 0xc9864080beb84a1e]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 7, .sample],
    [43], 8, #v[0x9d4c22c519456efc, 0x8afbeee8143e1a16, 0xa191969a84ae12ec, 0x40a717540c250855]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 8, .sample],
    [43], 9, #v[0x329b0eac474287fa, 0x4b4cf0028889f2d8, 0x7b7b793a58d67c56, 0x22d12a885e7f26c1]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 9, .sample],
    [43], 10, #v[0x2658e54de28edede, 0xe42abd73c765ea52, 0x161ba188239ba84a, 0xe6629fff9375d7e6]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 10, .sample],
    [43], 11, #v[0x2a7a61a6009c6e87, 0x84c87c728afc609d, 0x79dca30e8bf6c8af, 0x75ab02ac5e7872a]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 11, .sample],
    [43], 12, #v[0x7096bcea47e9, 0x8a7509a5c07b37ba, 0x3cef2193d8ee664e, 0xde22495639298938]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 12, .sample],
    [43], 13, #v[0x1fdc34f4254593ef, 0x9a3052351115b1ec, 0x5d06d1c1b963f54, 0x6afa9a9690d8f7ca]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 13, .sample],
    [43], 14, #v[0x4779a51fb461d42f, 0xc81b0f11a7a0ae3, 0x381b8c973b4dc96a, 0x6eb57c12c204f17b]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 14, .sample],
    [43], 15, #v[0xa0bb3fd458ad8269, 0x87d133afd85f95d5, 0x1fff595676845cf4, 0x8b0e33bf5d460532]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 15, .sample],
    [43], 16, #v[0x7fc6513e99fb79a9, 0xc85b83aec0b2f17c, 0x126661f3ba0f682c, 0x6fc3250c58930c1a]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 16, .sample],
    [43], 17, #v[0x5e5cc9f87b6b5b07, 0xcbb3f1166843cf56, 0xecf60c2008614cf0, 0xb9fa7ae1aea2acbb]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 17, .sample],
    [43], 18, #v[0x2810ddf40d5f44c6, 0x65979d744f16e224, 0xfa369220fe342370, 0x4c4e1b3561edfa3c]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 18, .sample],
    [43], 19, #v[0xab0597b0f5255764, 0xbd6c8867e6e54127, 0x5cb890d60a696b40, 0xa3542397cc1f02f8]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 19, .sample],
    [43], 20, #v[0xd39590e6e3cf8dda, 0xdc31c7f86d6b932a, 0xc042ef1cd12f1ea8, 0x3ba2d8817acda7bc]⟩,
  ⟨[.send 1, .grind 6, .samplePacked 20, .sample],
    [43], 21, #v[0xdc1d3774a9da576, 0x35baf52521ad754f, 0x89e4c55b6a4a7d09, 0xb2786963108bccd5]⟩,
  ⟨[.send 3, .sendPacked 9, .samplePacked 5, .grind 4, .samplePacked 9, .sendPacked 0, .sample, .grind 2, .sample, .sendPacked 17, .samplePacked 16, .send 1, .samplePacked 1],
    [14, 4], 33, #v[0xc7e3c65a6a35f5ee, 0xdc16c89ba504f0ab, 0xa00ec5e10e279542, 0xaf955631c2397e11]⟩,
  ⟨[.sendPacked 8, .sendPacked 8, .send 5, .sendPacked 1, .grind 3, .samplePacked 7, .samplePacked 8, .sample],
    [26], 16, #v[0x6fcd38dc32c28fc4, 0xc06c06ebc89e5793, 0xef19c0f3bb68b695, 0x3763efc4d5d40af8]⟩,
  ⟨[.grind 5, .samplePacked 1, .grind 5, .sample, .sendPacked 16, .grind 2, .samplePacked 30],
    [0, 36, 4], 32, #v[0xa4c5017f7f3113f8, 0x18a5d2c63b471654, 0xadbdc5b4eeca42ee, 0xc9f5b4087e551bc3]⟩,
  ⟨[.send 4, .grind 1, .samplePacked 8, .sendPacked 3, .send 4, .sample, .samplePacked 0, .sendPacked 0, .sample],
    [2], 10, #v[0xf7a316601fc2ad9, 0x3e4fe4b633ab1d2f, 0xcf03d8316449d5a5, 0x746ebfd8360d09f4]⟩]

#guard cases.length = 151

#guard cases.all Case.holds

/-! ## A packed draw after a grind, challenge by challenge -/

/-- A packed draw of nine after a `6`-bit grind (nonce `43`): the ground challenge, the grind
permutation's cells `2..8`, then the first cell of a permutation of its own. -/
def drawAfterGrind : List (UInt64 × UInt64) := [
  (0xac656335b5709e55, 0x46f490c524e77320),
  (0x55dd6a5909c75ff3, 0x93954c8560af067e),
  (0xd1032149560e7deb, 0xa47d623adf844f46),
  (0x3b7026762a6524ae, 0xbedd21c1dfc424bb),
  (0xf8e33a32777fd48, 0xf6a21e313762bd32),
  (0xedecd79180ef2e02, 0xd65671081d00b2b5),
  (0x15a33fff243d535b, 0x921a36a73c91483e),
  (0xb9861499961edd21, 0x449e9ff2ee355d6),
  (0xed3b9f1bdf4ee5cb, 0xb76830b1b0e6fab8)]

#guard (verifierChallenges [.send 1, .grind 6, .samplePacked 9] [43]).map
    (·.map fun c ↦ ((c.limb 0).lane, (c.limb 1).lane)) = some drawAfterGrind

/-! ## Rejections -/

-- A packed read, even of nothing, while a grind's challenge waits.
#guard (verifierChallenges [.send 1, .grind 6, .sendPacked 0, .sample] [43]).isNone

-- A packed read past the stream's end.
#guard (Id.run (run (m := Id) keccakF1600 (program [.sendPacked 3])
    ⟨⟨seed, [], none⟩, vals 0 2, [], []⟩)).isNone

end LeanVMTests.Protocol.Transcript
