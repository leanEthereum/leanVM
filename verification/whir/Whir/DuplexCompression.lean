import Whir.DuplexRefinement

/-! Executable BLAKE2s compression, hand-ported from RFC 7693 and the pinned
#552 `crates/primitives/src/hash/mod.rs`. Equality to machine-compiled Rust is
not claimed; known-answer and cross-language traces exercise this evaluator. -/
namespace Whir.DuplexCompression
open FiatShamirGame DuplexRefinement

def primitiveSourceSHA256 : String :=
  "8c8cb68504ed8552bb6e3b9e09efbfd493522c61120ce9d04a0cc1992e20150c"

def ivWords : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
    0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def sigma : Array (Array Nat) := #[
  #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
  #[14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
  #[11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
  #[7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
  #[9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
  #[2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
  #[12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
  #[13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
  #[6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
  #[10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

def lanes : Array (Nat × Nat × Nat × Nat) :=
  #[(0,4,8,12),(1,5,9,13),(2,6,10,14),(3,7,11,15),
    (0,5,10,15),(1,6,11,12),(2,7,8,13),(3,4,9,14)]

def rotate (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def mix (v : Array UInt32) (a b c d : Nat) (x y : UInt32) : Array UInt32 := Id.run do
  let mut v := v
  v := v.set! a (v[a]! + v[b]! + x)
  v := v.set! d (rotate (v[d]! ^^^ v[a]!) 16)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotate (v[b]! ^^^ v[c]!) 12)
  v := v.set! a (v[a]! + v[b]! + y)
  v := v.set! d (rotate (v[d]! ^^^ v[a]!) 8)
  v := v.set! c (v[c]! + v[d]!)
  v := v.set! b (rotate (v[b]! ^^^ v[c]!) 7)
  return v

def word {n : Nat} (bytes : Fin n → Byte) (i : Nat) : UInt32 :=
  (List.range 4).foldl (fun acc j =>
    if h : 4*i+j < n then acc ||| ((UInt32.ofNat (bytes ⟨4*i+j,h⟩).val) <<< UInt32.ofNat (8*j))
    else acc) 0

def digest (ws : Array UInt32) : Digest32 := fun i =>
  ⟨((ws[i.val / 4]!.toNat / 256^(i.val % 4)) % 256), Nat.mod_lt _ (by decide)⟩

def parameterIV : Digest32 := digest (ivWords.set! 0 (ivWords[0]! ^^^ 0x01010020))

def compress : Compression := fun h block counter last => Id.run do
  let hw := (Array.range 8).map (word h)
  let m := (Array.range 16).map (word block)
  let mut v := hw ++ ivWords
  v := v.set! 12 (v[12]! ^^^ counter.toUInt32)
  v := v.set! 13 (v[13]! ^^^ (counter >>> 32).toUInt32)
  if last then v := v.set! 14 (~~~v[14]!)
  for schedule in sigma do
    for g in [0:8] do
      let (a,b,c,d) := lanes[g]!
      v := mix v a b c d m[schedule[2*g]!]! m[schedule[2*g+1]!]!
  return digest ((Array.range 8).map fun i => hw[i]! ^^^ v[i]! ^^^ v[i+8]!)

/-- Ordinary one-block BLAKE2s-256 (inputs of length at most 64). -/
def hashBlock (bytes : Array Byte) : Digest32 :=
  compress parameterIV (padded bytes) (UInt64.ofNat bytes.size) true

/-- Ordinary BLAKE2s PoW test; not a claimed soundness amplification. -/
def powOK (base : Digest32) (nonce : Scalar24) (bits : Nat) : Bool :=
  let bs := List.ofFn base ++ List.ofFn nonce ++ littleWord 0x31574f502d534646
  let d := hashBlock bs.toArray
  let low := ByteCodec.decodeNat 8 (fun i => d ⟨i.val, by omega⟩)
  low % 2^bits == 0

def hex (bs : List Byte) : String :=
  String.ofList (bs.flatMap fun b =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[b.val / 16]!, digits[b.val % 16]!])

/-- RFC 7693 BLAKE2s-256 known-answer vectors, evaluated by the executable
compression (not native_decide and not an assumed oracle). -/
def knownAnswers : Bool :=
  hex (List.ofFn (hashBlock #[])) == "69217a3079908094e11121d042354a7c1f55b6482ca1a51e1b250dfd1ed0eef9" &&
  hex (List.ofFn (hashBlock #[97,98,99])) == "508c5e8c327c14e2e1a72ba34eeb452f37458b209ed63a294d999b4c86675982"

/-- Observable snapshot used by the source-pinned external Rust differential
probe: CV, active pending bytes, first flag, prior cursor, consumed cursor,
cached output block, nonmutating commitment. -/
def snapshot (label : String) (s : State) : String :=
  label ++ "|" ++ hex (List.ofFn s.cv) ++ "|" ++ hex s.pending.toList ++ "|" ++
  toString s.first ++ "|" ++ toString s.previous ++ "|" ++ toString s.consumed ++ "|" ++
  hex (List.ofFn s.output) ++ "|" ++ hex (List.ofFn (commitment compress s))

def traceDraw (label : String) (s : State) (n : Nat) : State × List String :=
  match squeeze compress s n with
  | .error e => (s, [label ++ ":error:" ++ reprStr e])
  | .ok (t, bs) => (t, [label ++ ":" ++ hex bs, snapshot label t])

def traceNonce (label : String) (s : State) (nonce : Concrete.E) (bits : Nat) : State × List String :=
  match verifyNonce compress powOK s (ByteCodec.encodeE nonce) bits with
  | .error e => (s, [label ++ ":error:" ++ reprStr e])
  | .ok (t, ok) => (t, [label ++ ":" ++ toString ok, snapshot label t])

/-- The same scenario was executed against the original pinned Rust source in
an external harness. The error-limit injection is harness-only, not an API. -/
def differentialTrace : List String := Id.run do
  let d : Digest32 := fun i => (wordsBlock [1,2,3,4]) ⟨i.val, by omega⟩
  let st : Digest32 := fun i => (wordsBlock [5,6,7,8]) ⟨i.val, by omega⟩
  let mut s := seed compress parameterIV d st
  let mut out := [snapshot "seed" s, snapshot "empty" (absorb compress s [])]
  s := absorb compress s ((List.range 64).map fun n => ⟨n % 256, Nat.mod_lt _ (by decide)⟩)
  out := out ++ [snapshot "held64" s]
  let held := traceDraw "held-final" s 3
  out := out ++ held.2
  s := absorb compress s [64]
  out := out ++ [snapshot "continued65" s]
  let p := traceDraw "partial3" s 3
  s := p.1
  out := out ++ p.2
  let clone := traceDraw "clone29" s 29
  out := out ++ clone.2 ++ (traceDraw "clone-next5" clone.1 5).2
  s := absorb compress s [201,202]
  out := out ++ [snapshot "switch-after3" s]
  let p := traceDraw "switch-out" s 35
  s := p.1
  out := out ++ p.2
  let p := traceNonce "nonce-zero" s ⟨1,2,3⟩ 0
  s := p.1
  out := out ++ p.2
  let p := traceNonce "nonce-one" s ⟨4,5,6⟩ 1
  s := p.1
  out := out ++ p.2
  let p := traceDraw "nonce-out" s 24
  s := p.1
  out := out ++ p.2
  let bitsBad := match verifyNonce compress powOK s (fun _ => 0) 64 with
    | .error .grindingBits => true | _ => false
  s := { s with consumed := maxCursor - 1 }
  let cursorBad := match squeeze compress s 2 with
    | .error .cursorExhausted => true | _ => false
  let vectorBad := match squeeze compress s 24 with
    | .error .cursorExhausted => true | _ => false
  return out ++ ["bits-limit:" ++ toString bitsBad, "cursor-limit:" ++ toString cursorBad,
    "vector-limit:" ++ toString vectorBad, "pow-base:" ++ hex (List.ofFn (powBase compress s 63))]

/-- Observed verbatim from the pinned Rust source in an external Rust 1.97
harness. Fixtures retain state as well as challenges and all export families.
The source's private cursor was changed only in that external harness to
exercise exhaustion without allocating 2^49 bytes. -/
def rustTraceFixture : List String := [
  "seed|f9b7641c1107505a7dc29b6e2f6d5419d81aa6e3db1582d0d3a980dad6c9aa88||true|0|0|0000000000000000000000000000000000000000000000000000000000000000|4243e176df0d5a88b09ce8f6459d98d7f4b289f646b6bb41a6cc73ff323d4fb0",
  "empty|f9b7641c1107505a7dc29b6e2f6d5419d81aa6e3db1582d0d3a980dad6c9aa88||true|0|0|0000000000000000000000000000000000000000000000000000000000000000|4243e176df0d5a88b09ce8f6459d98d7f4b289f646b6bb41a6cc73ff323d4fb0",
  "held64|f9b7641c1107505a7dc29b6e2f6d5419d81aa6e3db1582d0d3a980dad6c9aa88|000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f|true|0|0|0000000000000000000000000000000000000000000000000000000000000000|3fe42619bf69ded577ed52a1dcf47f4ca81ad8c6ad69b412610257628383db8f",
  "held-final:aa39f5",
  "held-final|b3847dfdbba2659c2082c59641ed04122ccbd7403be2c94ac26de99d268ecc6b||true|0|3|aa39f5e2c2dee165c4301949e5c312dd571e1b56a3684e47391b257d89b3eab3|bbf57ef6abbf095ed11df18ee51f2048f39db2b31b2c622c6982210dca674f76",
  "continued65|8918b3e8cf02981bb37faa42fd12a5344cb797984ca296d661cd6e2fdc73e922|40|false|0|0|0000000000000000000000000000000000000000000000000000000000000000|3c9d937dd79de7002235489eb991cc8fc239dcc4c2e93363b89c52aa3548db03",
  "partial3:4b1c12",
  "partial3|a1c6ea7ab811e887a75ac5a3093d430cb183e0f915a89c84c47234760bc915f4||true|0|3|4b1c1262a749750dbd6a94310607e3efadd9bca951ed52bc43a14f49573e47db|99f4dcf23768253b283078549d20e0ecaa5291e391d244484e004032e82217ab",
  "clone29:62a749750dbd6a94310607e3efadd9bca951ed52bc43a14f49573e47db",
  "clone29|a1c6ea7ab811e887a75ac5a3093d430cb183e0f915a89c84c47234760bc915f4||true|0|32|4b1c1262a749750dbd6a94310607e3efadd9bca951ed52bc43a14f49573e47db|398daa7b0892b7371b3ebb4a69ebe463028dc61c28a59c47c34ad413faf6b88f",
  "clone-next5:fdbfbedf61",
  "clone-next5|a1c6ea7ab811e887a75ac5a3093d430cb183e0f915a89c84c47234760bc915f4||true|0|37|fdbfbedf613888be548d62f49e4bb7f16f2c8994c34519fab7a4876b661037f7|3058d92de67869758f1c21ea5f1e45a4911a10cb921c1449d4db52cfb1fe60cf",
  "switch-after3|a1c6ea7ab811e887a75ac5a3093d430cb183e0f915a89c84c47234760bc915f4|c9ca|true|3|0|4b1c1262a749750dbd6a94310607e3efadd9bca951ed52bc43a14f49573e47db|a7419fc1a361d104e33d71e4cd22e0dee502d30e7f7152de78d74d6ddd1f4744",
  "switch-out:f76b7e535e58b7d79561247790580736a4c51ea1f0100e85c8e3b32dbe5e3d30c69cab",
  "switch-out|c7cedd71b8626817650cb469d6413991078483cdd972eb880c85013f54888fe9||true|0|35|c69cab915ec6fc162f0cf1421edabdfbf949798238daa1f89196808eec7eb0d2|730c83f9945acc52f98f5d3ef3c2c5b5087e438f6a1f65e763a0ef676ef33d92",
  "nonce-zero:false",
  "nonce-zero|279f961dcab6a188c6639ecc9089dfcdf18bd032c0afcb35fdd1079274e84be5||true|0|0|c69cab915ec6fc162f0cf1421edabdfbf949798238daa1f89196808eec7eb0d2|d20b6d5da7cec21b26a8984945210db60552a526f864d48cd5aa3f03caa080ba",
  "nonce-one:true",
  "nonce-one|20b039e7908ab97ddf2ea9dca086f3a4a3fc78f1778cf367597594910a24506c||true|0|0|c69cab915ec6fc162f0cf1421edabdfbf949798238daa1f89196808eec7eb0d2|427e62417ffdeb3b15e5fc9b15b40951f83003fd704b0c33b4641d26f88e42f8",
  "nonce-out:e30163f8a9ba146e7cd0dd0e3d6da1d9d7b867dd43e8cccd",
  "nonce-out|20b039e7908ab97ddf2ea9dca086f3a4a3fc78f1778cf367597594910a24506c||true|0|24|e30163f8a9ba146e7cd0dd0e3d6da1d9d7b867dd43e8cccdeb53ee7acc5b1d67|8e331280b224acf3b4f68ddd86e5f0f1345b1fafada4e60c02b6f07fb45cc418",
  "bits-limit:true", "cursor-limit:true", "vector-limit:true",
  "pow-base:6cf65dfb60d1c8a81f229ce0a191d0d1479429ee015618b1b74d3d2259a85271"]

def differentialMatches : Bool := differentialTrace == rustTraceFixture

def apiTrace : List String := Id.run do
  let d : Digest32 := fun i => (wordsBlock [1,2,3,4]) ⟨i.val, by omega⟩
  let st : Digest32 := fun i => (wordsBlock [5,6,7,8]) ⟨i.val, by omega⟩
  let s := observe compress (seed compress parameterIV d st) ⟨9,10,11⟩
  let .ok (s,n) := grind compress powOK s 3 | return ["api-grind3:error"]
  let mut out := ["api-grind3:" ++ toString n, snapshot "api-grind3" s]
  let .ok (s,xs) := sampleVec compress s 3 | return ["api-vector:error"]
  out := out ++ ["api-vector:" ++ hex (xs.flatMap (fun x => List.ofFn (ByteCodec.encodeE x))),
    snapshot "api-vector" s]
  let .ok (s,n) := grind compress powOK s 0 | return ["api-grind0:error"]
  out := out ++ ["api-grind0:" ++ toString n, snapshot "api-grind0" s]
  for (first,last,len,previous) in
      [(true,false,63,0),(false,true,1,1),(true,true,0,0),(true,true,65,0),(true,true,64,2^49)] do
    let rejected := match checkedAbsorbTweak first last len previous with
      | .error _ => true | .ok _ => false
    out := out ++ ["api-tweak-reject:" ++ toString rejected]
  return out ++ ["api-tweak-boundary:" ++ toString (absorbTweak true true 64 maxCursor)]

def rustApiFixture : List String := [
  "api-grind3:1",
  "api-grind3|d6d61dc3f4a842892b2d816deaf911c1ff44896b6a0893bab457d4435f6146f5||true|0|0|0000000000000000000000000000000000000000000000000000000000000000|80990a0f41fdb6fa0c86c237dc3d21029a9011f4f7d3a1cdc2e25cc32e15c293",
  "api-vector:0989abe44a783a912d29a169e0b83f808b2d6cd8cc0c1652bd9ff61b30484260b76e9f6d1b25b94db5ab2334186c9efea849323576c2aab71ddf33f809ff4a39aae0c1255b4bb2d8",
  "api-vector|d6d61dc3f4a842892b2d816deaf911c1ff44896b6a0893bab457d4435f6146f5||true|0|72|aae0c1255b4bb2d82f916cf475ad0716c8e25aaf516026a43603cb36c96d56bf|be23b5805506586077b6ef9e4d006c1067d2218bb51670f2fcc2edfed1ec8220",
  "api-grind0:0",
  "api-grind0|143b9f06ddb8b4cc02a1723a20943ff29da1cf1341ed18eb41dcb28e28ba8024||true|0|0|aae0c1255b4bb2d82f916cf475ad0716c8e25aaf516026a43603cb36c96d56bf|86c2ecb55c84fe50bbfac2b939c219472682b55c7b375e9ee88a81565dd9d79d",
  "api-tweak-reject:true", "api-tweak-reject:true", "api-tweak-reject:true",
  "api-tweak-reject:true", "api-tweak-reject:true", "api-tweak-boundary:324822123124097023"]

def apiMatches : Bool := apiTrace == rustApiFixture

end Whir.DuplexCompression
