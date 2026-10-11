import LeanSphincs.Constants
import LeanSphincs.Types
import LeanSphincs.TweakHash
import LeanSphincs.Fts
import LeanSphincs.Ots
import LeanSphincs.Verify

/-!
# `LeanSphincs`

An executable specification of leanSPHINCS verification over bytes: stateless SPHINCS+ over BLAKE2s, with WOTS+C
and FORS+C.

# Provenance

leanSPHINCS has no reference implementation or specification outside this repository. Its definition is the guest
program `programs/leansphincs/guest/src/{lib,ots,fts}.rs`, which states it is "byte for byte the scheme of the
leanSPHINCS specification" (lib.rs line 19). These modules transcribe that code's verifier, definition by
definition, each citing the lines it transcribes, over the bytes the guest's little-endian words stand for. BLAKE2s
is the vendored RFC 7693 transcription `EthCryptographySpecs.Xmss.Blake2s.hash`.

What pins the transcription is the known answer the host pins
(`programs/leansphincs/host/src/lib.rs`, `leansphincs_is_the_specified_scheme`): the public key's bytes and the
BLAKE2s of the signature's serialization, for a fixed seed and message. `LeanSphincs.Kat` checks this `verify`
accepts that signature, whose bytes hash to the pinned digest, and rejects it with one byte changed.
-/
