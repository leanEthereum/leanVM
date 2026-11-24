module

public import Statement.Verifier.Layout
public import Statement.Verifier.Transcript

/-!
# Ring switching (`crates/verifier/src/ring_switch.rs`)

The 64 claims `s[i] = z(i, point)` on `q_keccak`'s bit slices become one dense claim
`Σ_u W(u) q_keccak(u) = target` on the committed column. The map is `Φ(v) = Σ_p f_p Ψ(v)^(2^(8p))`
of the inner stage `Ψ(v) = Σ_b g_b v^(2^b)`, sixteen challenges, `f` then `g` (Annex A).
-/

@[expose] public section

namespace LeanVM.Protocol.Verifier

open LeanVM.Parameters
open LeanVM.Semantics
open LeanVM.Protocol.Compile

/-- `RING_MAP_WIDTH`: `Φ`'s challenges come in two rows of this many, `f_p` then `g_b`
(`ring_switch.rs`). -/
def ringMapWidth : ℕ := 8

/-- `frobenius_8(value, p)`: `value^(2^(8p))`, by `8p` squarings (`ring_switch.rs`). -/
def frobenius8 (value : E) (p : ℕ) : E := value ^ 2 ^ (ringMapWidth * p)

/-- `ring_psi(value, g)`: the inner stage `Ψ(v) = Σ_b g_b v^(2^b)` (`ring_switch.rs`). -/
def ringPsi (value : E) (g : List E) : E :=
  (g.foldl (fun (acc : E × E) gB ↦ (acc.1 + gB * acc.2, acc.2 * acc.2)) (0, value)).1

/-- `ring_target(s, f, g)`: `T = Σ_i x^i Φ(s_i) = Σ_p f_p (Σ_i z_p^i Ψ(s_i))^(2^(8p))`, with
`z_p = x^(2^(64 - 8p))`, `p` from `7` down to `0`, `z` squared eight times a step from `x`
(`ring_switch.rs`). -/
def ringTarget (s f g : List E) : E :=
  let images := s.map (ringPsi · g)
  ((List.range ringMapWidth).reverse.foldl (fun (acc : E × E) p ↦
    let z := frobenius8 acc.2 1
    (acc.1 + f.getD p 0 * frobenius8 (polyEval images z) p, z)) (0, gen)).1

/-- `ring_coefficients(f, g)`: the same map as a Frobenius sum, `Φ(v) = Σ_{k < 64} c_k v^(2^k)`,
`c_(8p+b) = f_p · g_b^(2^(8p))` (`ring_switch.rs`). -/
def ringCoefficients (f g : List E) : List E :=
  (f.foldl (fun (acc : List E × List E) fP ↦
    (acc.1 ++ acc.2.map (fP * ·), acc.2.map (frobenius8 · 1))) ([], g)).1

/-- `ring_weight(r, r_prime, coefficients)`: `W(u) = Φ(eq(r, u))` at the opening's point,
`Σ_k c_k Π_n (1 + r_n^(2^k) + r'_n)` (`ring_switch.rs`). -/
def ringWeight (r rPrime coefficients : List E) : E :=
  (coefficients.foldl (fun (acc : E × List E) c ↦
    let product := (List.zip acc.2 rPrime).foldl
      (fun product (value, challenge) ↦ product * (1 + value + challenge)) c
    (acc.1 + product, acc.2.map fun value ↦ value * value)) (0, r)).1

/-- `ring_switch(point, s, transcript)` (`ring_switch.rs`): one grind for the map's sixteen
challenges and the stacked opening's batching challenge drawn next, the map, and the target `T`
and the weight `W(u) = Φ(eq(point, u))` as a function of the opening point. -/
def ringSwitch (point s : List E) : VerifierProgram (E × (List E → E)) := do
  VerifierProgram.grindProofOfWork Whir.batchGrindingBits
  let challenges ← VerifierProgram.sampleChallenges (2 * ringMapWidth)
  let f := challenges.take ringMapWidth
  let g := challenges.drop ringMapWidth
  let coefficients := ringCoefficients f g
  let target := ringTarget s f g
  return (target, fun rPrime ↦ ringWeight point rPrime coefficients)

end LeanVM.Protocol.Verifier

end
