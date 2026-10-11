module

public import LeanVMCircuits.Blake2s.Export

@[expose] public section

/-!
Rust for the BLAKE2s compression, one line per register of the checked program.

Each operation becomes the call `Op.steps` describes: `add` is `wrapping_add32` on its registers, an odd literal's
addition `wrapping_add32` on the literal's wires, an even literal's `add_even32` (the low bit passed through, then
`wrapping_add31` on the upper bits), and `xor_rotr32` the XOR of rotated bits. `Export.adder32_call` and
`Export.adder31_call` prove those calls are the artifact's products and sums.
-/

namespace LeanVMCircuits.Blake2s.Emit

open Compress Rfc7693

def hex (k : Word) : String := "0x" ++ String.ofList (Nat.toDigits 16 k.toNat)

def register (r : ℕ) : String := s!"r{r}"

/-- The 32 registers before the rounds, as `Compress.register` builds them from the ports. Literal registers no
operation names are left out: a literal addend is written into its addition. -/
def initial : List String :=
  (List.range 8).map (fun r => s!"    let r{r} = h[{r}];") ++
  (List.range 16).map (fun r => s!"    let r{8 + r} = m[{r}];") ++
  (List.range 4).map (fun i => s!"    let r{24 + i} = literal32({hex IV[i]!});") ++
  [s!"    let r28 = xor32(c, &literal32({hex IV[4]}), &low32(t));",
   s!"    let r29 = xor32(c, &literal32({hex IV[5]}), &high32(t));",
   s!"    let r30 = xor32(c, &literal32({hex IV[6]}), f0);",
   s!"    let r31 = literal32({hex IV[7]});"]

def rust : Op → String
  | .add x y => s!"wrapping_add32(c, &r{x}, &r{y})"
  | .addOdd k y => s!"wrapping_add32(c, &literal32({hex k}), &r{y})"
  | .addEven k y => s!"add_even32(c, {hex k}, &r{y})"
  | .xorRotr r x y => s!"xor_rotr32(c, &r{x}, &r{y}, {r.val})"

def helpers : String := "
/// A 32-bit literal's wires: one where the bit is set, the structural zero elsewhere.
fn literal32(k: u32) -> [Wire; 32] {
    std::array::from_fn(|i| Wire::constant(k >> i & 1 == 1))
}

/// The low half of a 64-bit port.
fn low32(t: &[Wire; 64]) -> [Wire; 32] {
    std::array::from_fn(|i| t[i])
}

/// The high half of a 64-bit port.
fn high32(t: &[Wire; 64]) -> [Wire; 32] {
    std::array::from_fn(|i| t[32 + i])
}

/// `x ^ y`, free.
fn xor32(c: &mut Builder, x: &[Wire; 32], y: &[Wire; 32]) -> [Wire; 32] {
    std::array::from_fn(|i| c.xor(x[i], y[i]))
}

/// `(x ^ y) >>> r`, free.
fn xor_rotr32(c: &mut Builder, x: &[Wire; 32], y: &[Wire; 32], r: usize) -> [Wire; 32] {
    std::array::from_fn(|i| c.xor(x[(i + r) % 32], y[(i + r) % 32]))
}

/// `k + y` for an even literal `k`: the low bit is `y`'s, and `k / 2` is added to the upper 31 bits.
fn add_even32(c: &mut Builder, k: u32, y: &[Wire; 32]) -> [Wire; 32] {
    let half: [Wire; 31] = std::array::from_fn(|i| Wire::constant(k >> (i + 1) & 1 == 1));
    let upper: [Wire; 31] = std::array::from_fn(|i| y[i + 1]);
    let sum = wrapping_add31(c, &half, &upper);
    std::array::from_fn(|i| if i == 0 { y[0] } else { sum[i - 1] })
}
"

/-- The compression function, its registers numbered as in `program`, then the output `h ^ v_low ^ v_high`. -/
def emit : Except String String := do
  let ops := program.ops
  unless ops.all Op.valid do throw "an operation's literal has the wrong parity"
  let products := (ops.map fun
    | .add _ _ | .addOdd _ _ => 31
    | .addEven _ _ => 30
    | .xorRotr _ _ _ => 0).sum
  unless products == 14878 do throw s!"unexpected product count {products}"
  let used := ops.flatMap (fun
    | .add x y | .xorRotr _ x y => [x, y]
    | .addOdd _ y | .addEven _ y => [y]) ++ program.lanes.toList
  let initial := (initial.zipIdx.filter fun (_, r) => used.contains r).map Prod.fst
  let body := (ops.zipIdx.map fun (op, i) => s!"    let r{32 + i} = {rust op};")
  let lanes := String.intercalate ", " (program.lanes.toList.map fun r => s!"&r{r}")
  let header := [
    "/// The checked BLAKE2s compression (`LeanVMCircuits.Blake2s.Compress`), its operations in program order.",
    "///",
    "/// `t` and `f0` are the counter and the finalization word, `h` and `m` the chaining value's and the message's",
    "/// 32-bit words; output bit `32 i + j` is bit `j` of the new chaining value's word `i`.",
    "pub fn blake2s(c: &mut Builder, t: &[Wire; 64], f0: &[Wire; 32], h: &[[Wire; 32]; 8], m: &[[Wire; 32]; 16]) -> [Wire; 256] {"]
  let footer := [
    s!"    let lanes: [&[Wire; 32]; 16] = [{lanes}];",
    "    std::array::from_fn(|k| {",
    "        let (i, j) = (k / 32, k % 32);",
    "        let low = c.xor(h[i][j], lanes[i][j]);",
    "        c.xor(low, lanes[i + 8][j])",
    "    })",
    "}"]
  return String.intercalate "\n" (header ++ initial ++ body ++ footer) ++ "\n" ++ helpers

end LeanVMCircuits.Blake2s.Emit
