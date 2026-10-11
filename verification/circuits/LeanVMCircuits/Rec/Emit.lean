module

public import LeanVMCircuits.Rec.Tables
public import LeanVMCircuits.Rec.Duplex

@[expose] public section

/-!
Rust for the recursion tables: each slot's forms as `leaf::Coord` values, each identity as coefficient words, printed
from the same `Form` and `Identity` data the theorems of `LeanVMCircuits.Rec.Tables` are about. Products of `K`
elements computed by the proven carry-less word product `Rec.mul` (`Rec.ev_mul`) pin the prover's field to `K`.
-/

namespace LeanVMCircuits.Rec.Emit

def hex (w : ℕ) : String := "0x" ++ String.ofList (Nat.toDigits 16 w)

partial def form : Form → String
  | .const w => s!"Const(F64({hex w}))"
  | .col c => s!"Col({c})"
  | .prod a b => s!"Prod({a}, {b})"
  | .sum terms => "Sum(vec![" ++ String.intercalate ", " (terms.map form) ++ "])"

def Form.isSum : Form → Bool
  | .sum _ => true
  | _ => false

def slots (name doc : String) (table : List (List Form)) : String :=
  let arms := table.zipIdx.map fun (slot, s) =>
    s!"        {s} => [" ++ String.intercalate ", " (slot.map form) ++ "],"
  -- A table with no sum allocates nothing, so its function is `const`.
  let qualifier := if table.any (·.any Form.isSum) then "fn" else "const fn"
  s!"/// {doc}\npub(crate) {qualifier} {name}(s: usize) -> Option<[Coord; 4]> \{\n    Some(match s \{\n" ++
    String.intercalate "\n" arms ++ "\n        _ => return None,\n    })\n}\n"

def identity (id : Identity) : String :=
  let linear := String.intercalate ", " (id.linear.map fun (c, w) => s!"({c}, {hex w})")
  let prods := String.intercalate ", " (id.prods.map fun (a, b, w) => s!"({a}, {b}, {hex w})")
  s!"    (&[{linear}], &[{prods}]),"

def identities (name doc : String) (ids : List Identity) : String :=
  s!"/// {doc}\npub(crate) const {name}: &[Identity] = &[\n" ++ String.intercalate "\n" (ids.map identity) ++ "\n];\n"

/-- Sample products in `K`, by the word product proven to be `K`'s multiplication. -/
def products : List (ℕ × ℕ × ℕ) :=
  let samples : List ℕ := [0, 1, 2, 0x1b, 2 ^ 63, 2 ^ 64 - 1, 0x5c62236777028505, 0x53cad161bf5a89c7,
    0x0123456789abcdef, 0xfedcba9876543210]
  samples.flatMap fun a => samples.map fun b => (a, b, mul a b)

def slotIndex (name doc : String) (s : ℕ) : String := s!"/// {doc}\npub(crate) const {name}: usize = {s};\n"

/-- The slot indices the builder writes, from the names the row theorems use. -/
def slotIndices : String :=
  slotIndex "ARITH_A" "`EMUL`'s and `EXK`'s first factor." arithA ++
  slotIndex "ARITH_B" "`EMUL`'s second factor, `EXK`'s `K` factor." arithB ++
  slotIndex "ARITH_D" "`EMUL`'s and `EXK`'s addend." arithD ++
  slotIndex "ARITH_C" "`EMUL`'s and `EXK`'s result." arithC ++
  slotIndex "HASH_H" "`HASH`'s chaining value." hashSlotH ++
  slotIndex "HASH_TF" "`HASH`'s counter and finalization word." hashSlotTF ++
  slotIndex "HASH_MUX" "`HASH`'s mux (`Rec.node_row`)." hashSlotMux ++
  slotIndex "HASH_SEL" "`HASH`'s mux bit." hashSlotSel ++
  slotIndex "HASH_X" "`HASH`'s message words four to six as an element." hashSlotX ++
  slotIndex "HASH_DS" "`HASH`'s message word seven." hashSlotDs ++
  slotIndex "HASH_OUT" "`HASH`'s output." hashSlotOut ++
  slotIndex "HASH_CH" "`HASH`'s output's first three words as an element (`Rec.hash_outputs`)." hashSlotCh ++
  slotIndex "HASH_M" "`HASH`'s first message word, the other seven after it." hashSlotM ++
  slotIndex "SPLIT_WORD" "`SPLIT`'s word." splitSlotWord ++
  slotIndex "SPLIT_BITS" "`SPLIT`'s first bit, the other 63 after it." splitSlotBits ++
  slotIndex "CAST_DIGEST" "`CAST`'s digest." castDigest ++
  slotIndex "CAST_ELEMENT" "`CAST`'s element of the first three words." castElement ++
  slotIndex "CAST_HALVES" "`CAST`'s low half, the high half after it." castHalves ++
  slotIndex "CAST_WORDS" "`CAST`'s first word, the other three after it." castWords

/-- `[a, b, c, d]` as a Rust array of words. -/
def words4Lit (w : Fin 4 → BitVec 64) : String :=
  "[" ++ String.intercalate ", " ((List.ofFn w).map fun x => hex x.toNat) ++ "]"

/-- RFC 7693 chaining values after `n` zero blocks, the native `zero_prefix`'s. -/
def zeroPrefixes : List String :=
  (List.range 4).map fun n => words4Lit (digest (absorb paramIV 0 (List.replicate n (Vector.replicate 16 0))))

/-- `absorb_tweak` samples: every role, full and partial lengths, cursors at both ends. -/
def tweakSamples : List (Bool × Bool × ℕ × ℕ) :=
  [true, false].flatMap fun first => [true, false].flatMap fun last =>
    ([8, 24, 64].filter fun len => last || len = 64).flatMap fun len =>
      ((if first then [0, 24, 2 ^ 49 - 1] else [0]).map fun previous => (first, last, len, previous))

/-- The native constants the recursion circuit's hashes and transcript take, as the Lean transcriptions give them:
`Rec.paramIV`, RFC 7693's chaining values of zero blocks, `fiat_shamir`'s role tags, `POW_TAG` and `absorb_tweak`. -/
def nativePins : String :=
  "/// `PARAM_IV` (`Rec.paramIV`).\n#[cfg(test)]\npub(crate) const PARAM_IV_WORDS: [u64; 4] = " ++
    words4Lit (digest paramIV) ++ ";\n\n" ++
  "/// The chaining values after zero, one, two and three zero blocks (`Rec.absorb`).\n#[cfg(test)]\n" ++
    "pub(crate) const ZERO_PREFIXES: [[u64; 4]; 4] = [" ++ String.intercalate ", " zeroPrefixes ++ "];\n\n" ++
  "/// `SEED`, `OUTPUT`, `COMMIT`, `POW_BASE`, `NONCE` and `POW_TAG` (`Rec.seedTag` and the rest).\n#[cfg(test)]\n" ++
    "pub(crate) const DUPLEX_TAGS: [u64; 6] = [" ++ String.intercalate ", "
      ([seedTag, outputTag, commitTag, powBaseTag, nonceTag, powTag].map fun t => hex t.toNat) ++ "];\n\n" ++
  "/// `(first, last, len, previous, absorb_tweak(first, last, len, previous))` (`Rec.tweak`).\n#[cfg(test)]\n" ++
    "pub(crate) const ABSORB_TWEAKS: &[(bool, bool, usize, u64, u64)] = &[\n" ++
    String.intercalate "\n" (tweakSamples.map fun (f, l, len, p) =>
      s!"    ({f}, {l}, {len}, {hex p}, {hex (tweak f l len p).toNat}),") ++ "\n];\n"

def emit : String :=
  "// Generated by verification/circuits/GenerateRec.lean from LeanVMCircuits.Rec.Tables. Do not edit.\n" ++
  "//! The recursion tables' slot forms and identities, proven in `LeanVMCircuits.Rec.Tables`.\n\n" ++
  "use crate::leaf::Coord::{self, Col, Const, Prod, Sum};\nuse primitives::field::F64;\n\n" ++
  "/// An identity: `(column, coefficient)` terms and `(column, column, coefficient)` products, coefficients as\n" ++
  "/// `K` words, summing to zero.\npub(crate) type Identity = (&'static [(usize, u64)], &'static [(usize, usize, u64)]);\n\n" ++
  slotIndices ++ "\n" ++
  slots "emul" "`EMUL`'s slot `s`: `a`, `b`, `d`, then `c = a·b + d` in `E` (`Rec.emul_spec`)." emul ++ "\n" ++
  slots "exk" "`EXK`'s slot `s`: `a`, `k`, `d`, then `c = a·k + d` (`Rec.exk_spec`)." exk ++ "\n" ++
  slots "hash" "`HASH`'s slot `s` over its ports and its mux bit (`Rec.hash_mux`)." hash ++ "\n" ++
  slots "split" "`SPLIT`'s slot `s`: the word, then its bits (`Rec.split_spec`)." split ++ "\n" ++
  slots "cast" "`CAST`'s slot `s`: four words as a digest, an `E` element, two halves and four words." cast ++ "\n" ++
  identities "HASH_IDENTITIES" "`HASH`'s identities: its mux bit is Boolean (`Rec.hash_mux`)." hashIdentities ++
  "\n" ++
  identities "SPLIT_IDENTITIES" "`SPLIT`'s identities: the word is its bits' sum, each Boolean (`Rec.split_spec`)."
    splitIdentities ++ "\n" ++
  "/// `(a, b, a·b)` in `K`, by the carry-less product proven to be `K`'s multiplication (`Rec.ev_mul`).\n" ++
  "#[cfg(test)]\npub(crate) const K_PRODUCTS: &[(u64, u64, u64)] = &[\n" ++
  String.intercalate "\n" (products.map fun (a, b, c) => s!"    ({hex a}, {hex b}, {hex c}),") ++ "\n];\n\n" ++
  nativePins

end LeanVMCircuits.Rec.Emit
