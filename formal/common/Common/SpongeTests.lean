import Common.Sponge

/-! Keccak-256 of `Common/Sponge.lean` on the test vectors of leanVM's `hash.rs`, evaluated: a file
of its own, outside the module system, since a module cannot evaluate its own definitions. -/

namespace Common

/-! The test vectors of `hash.rs` (from the `sha3` crate's `Keccak256`), on each side of a block
boundary. -/

#guard hexOfBytes (keccak256 (countingBytes 0)).toList ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
#guard hexOfBytes (keccak256 (countingBytes 1)).toList ==
  "bc36789e7a1e281436464229828f817d6612f7b477d66591ff96a9e064bcc98a"
#guard hexOfBytes (keccak256 (countingBytes 135)).toList ==
  "cbdfd9dee5faad3818d6b06f95a219fd290b0e1706f6a82e5a595b9ce9faca62"
#guard hexOfBytes (keccak256 (countingBytes 136)).toList ==
  "7ce759f1ab7f9ce437719970c26b0a66ff11fe3e38e17df89cf5d29c7d7f807e"
#guard hexOfBytes (keccak256 (countingBytes 137)).toList ==
  "ac73d4fae68b8453f764007c1a20ce95994187861f0c3227a3a8e99a73a3b1db"
#guard hexOfBytes (keccak256 (countingBytes 272)).toList ==
  "fdf2ec49e749960d3c8521a0219af8d03e30e2b3bf19bd16150ee0eaf133d66e"

end Common
