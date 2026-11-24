/-
  LeanVM.Protocol.Keccak.RmfeDerive

  The verifier's `RMFE_EMBED` and `RMFE_PROJECT` derived from seven irreducible moduli, and the
  derivation checked equal to the statement's literals by the kernel.
-/

module

public import Statement.Verifier.Keccak
public import Statement.CostMachine

/-!
# The embedding, derived

`rmfeEmbed` and `rmfeProject` (`Statement/Verifier/Keccak.lean`) are `RMFE_EMBED` and `RMFE_PROJECT`
of `crates/verifier/src/keccak.rs`, copied. Here they are derived (`rmfe`): sixteen bits are glued
by the Chinese remainder theorem from the residues modulo seven irreducible binary polynomials
(`rmfeFactors`), the last bit riding the leading coefficient, which the residues do not see; and
`rmfe_eq` checks the derivation equal to the literals, by the kernel.

Binary polynomials are natural numbers, bit `i` the coefficient of `x^i`. `carrylessDivmod a f`
is bounded by the fuel of the bit length of `a` plus one (each step lowers the bit length of the
remainder when `f ≠ 0`; `f = 0` is never passed). A factor's inverse is the first `g` in
`1 .. 2^degree - 1` that inverts the cofactor modulo the factor, by `List.find?`, `0` if none
(every factor of `rmfeFactors` is irreducible, so one is found).
-/

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters LeanVM.Cost

@[expose] public section

/-- The moduli the embedding is glued from, with the bits each holds. -/
def rmfeFactors : List (ℕ × ℕ) :=
  [(0b10, 1), (0b11, 1), (0b1011, 2), (0b1101, 2), (0b100101, 3), (0b101001, 3), (0b101111, 3)]

/-- The loop of `carrylessDivmod`: while the remainder is nonzero and no shorter than `f`,
subtract `f` shifted under its leading bit. -/
def carrylessDivmodAux : (fuel f quotient a : ℕ) → ℕ × ℕ
  | 0, _, quotient, a => (quotient, a)
  | fuel + 1, f, quotient, a =>
    if a ≠ 0 ∧ bitLength f ≤ bitLength a then
      let shift := bitLength a - bitLength f
      carrylessDivmodAux fuel f (quotient ||| (1 <<< shift)) (a ^^^ (f <<< shift))
    else (quotient, a)

/-- `carrylessDivmod a f`: the quotient and remainder of binary polynomials. -/
def carrylessDivmod (a f : ℕ) : ℕ × ℕ := carrylessDivmodAux (bitLength a + 1) f 0 a

/-- The parity of the set bits. -/
def bitParity (n : ℕ) : ℕ := ((List.range (bitLength n)).countP fun i ↦ n.testBit i) % 2

/-- The product of the moduli, by `carryless`. -/
def rmfeModulus : ℕ :=
  match rmfeFactors.map Prod.fst with
  | [] => 0
  | f :: fs => fs.foldl carryless f

/-- One factor's share of `rmfe`: its bits' embeddings (the residues,
lifted through the Chinese remainder theorem), and per bit the projection's mask, the product
coefficients whose parity is the bit. -/
def rmfeFactor (modulus f bits : ℕ) : List ℕ × List ℕ :=
  let cofactor := (carrylessDivmod modulus f).1
  let degree := bitLength f - 1
  let inverse := (((List.range (2 ^ degree)).drop 1).find? fun g ↦
    (carrylessDivmod (carryless (carrylessDivmod cofactor f).2 g) f).2 = 1).getD 0
  let lift := (carrylessDivmod (carryless cofactor inverse) modulus).2
  -- A residue is the polynomial taking the bits as its values at 0, 1 and infinity.
  let residues : List ℕ := if bits = 1 then [1] else if bits = 2 then [0b11, 0b10]
    else [0b011, 0b010, 0b110]
  let embed := residues.map fun r ↦ (carrylessDivmod (carryless lift r) modulus).2
  let masks := (List.range productBits).foldl (fun masks c ↦
    let g := (carrylessDivmod (1 <<< c) f).2
    let atZero := g % 2
    let atOne := bitParity g
    let values : List ℕ := if bits = 1 then [if f = 0b10 then atZero else atOne]
      else if bits = 2 then [atZero, atOne] else [atZero, atOne, g >>> 4]
    List.zipWith (fun mask value ↦ mask ||| (value <<< c)) masks values)
    (List.replicate bits 0)
  (embed, masks)

/-- The embedding: sixteen bits embed in a binary polynomial of degree at
most `23`, and a product of two embeddings projects to the AND of what they embed. Each unit
vector's embedding, and per bit of the projection the product coefficients it is the parity of;
the last bit rides the leading coefficient, which the residues do not see. -/
def rmfe : List ℕ × List ℕ :=
  let (embed, project) := rmfeFactors.foldl (fun (acc : List ℕ × List ℕ) (f, bits) ↦
    let (e, p) := rmfeFactor rmfeModulus f bits
    (acc.1 ++ e, acc.2 ++ p)) ([], [])
  (embed ++ [rmfeModulus], project ++ [1 <<< (productBits - 1)])

set_option maxRecDepth 100000 in
/-- **The derivation gives the literals** of `keccak.rs`. -/
theorem rmfe_eq : rmfe = (rmfeEmbed, rmfeProject) := by decide +kernel

end

end LeanVM.Protocol.Verifier
