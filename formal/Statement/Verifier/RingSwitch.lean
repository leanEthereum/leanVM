module

public import Statement.Verifier.Sumcheck

/-!
# Ring switching (`crates/verifier/src/ring_switch.rs`)

The 64 slices a reduction leaves, `s[i] = Σ_p scale_p z_p(i, point_p)` over pieces of committed
columns (`RingClaim`), become one dense claim `Σ_u W(u) column(u) = T` on the stack: the Keccak
reduction's on `q_keccak` and the link's on the pointer columns, merged by powers of `rho`. The map
is `Φ(v) = Σ_p f_p Ψ(v)^(2^(8p))` of the inner stage `Ψ(v) = Σ_b g_b v^(2^b)`, sixteen challenges,
`f` then `g` (Annex A).
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

/-- One piece of a ring-switched claim (`RingPiece`, `ring_switch.rs`): the slices of the column at
`placement` (the whole stack for `none`) at `point`, scaled by `scale`. A column is one piece. -/
structure RingPiece where
  /-- `placement`: where the piece sits, `none` for the whole stack. -/
  placement : Option Placement
  /-- `point`: the piece's point, over its own variables. -/
  point : List E
  /-- `scale`: the piece's scale. -/
  scale : E
  deriving Inhabited

/-- The 64 claims `s[i] = Σ_p scale_p z_p(i, point_p)` on the bit slices of the pieces' columns
(`RingClaim`, `ring_switch.rs`). -/
structure RingClaim where
  /-- `pieces`: the pieces. -/
  pieces : List RingPiece
  /-- `slices`: the 64 slice values. -/
  slices : List E
  deriving Inhabited

/-- `frobenius(x)` (`ring_switch.rs`): the Frobenius powers `x^(2^k)` for `k < 64`, by squaring. -/
def frobenius (x : E) : List E :=
  ((List.range kBits).foldl (fun (acc : List E × E) _ ↦ (acc.1 ++ [acc.2], acc.2 * acc.2))
    ([], x)).1

/-- The pieces at one point (`PointGroup`, `ring_switch.rs`): the point's Frobenius powers,
coordinate by coordinate, and each piece's placement and the Frobenius powers of its scale. The
pointer columns of one table share their table's row point. -/
structure RingPointGroup where
  /-- `point`: each coordinate's 64 Frobenius powers. -/
  point : List (List E)
  /-- `pieces`: each piece's placement (`none` for the whole stack) and its scale's powers. -/
  pieces : List (Option Placement × List E)
  deriving Inhabited

/-- `ring_weight(groups, x, coefficients)` (`ring_switch.rs`): the weight
`W(u) = Σ_p Φ(scale_p eq(r_p, u))`, extended and evaluated by the opening at the stack point `x`:
`Σ_k c_k Π_n (1 + r_n^(2^k) + x_n) Σ_p above_p(x) scale_p^(2^k)`, the product shared by the pieces at
one point, `above_p` the equality weight above the piece's placement (`1` for the whole stack). -/
def ringWeight (groups : List RingPointGroup) (x coefficients : List E) : E :=
  sumE (groups.map fun group ↦
    let n := group.point.length
    let aboves := group.pieces.map fun piece ↦
      match piece.1 with
      | some placement => placement.eqAbove x
      | none => 1
    sumE (coefficients.zipIdx.map fun (c, k) ↦
      let product := (group.point.zip (x.take n)).foldl
        (fun acc (powers, xn) ↦ acc * (1 + powers.getD k 0 + xn)) c
      let scales := sumE ((group.pieces.zip aboves).map fun (piece, above) ↦
        above * piece.2.getD k 0)
      product * scales))

/-- `ring_switch`'s merge, at its challenges (`ring_switch.rs`): claim `j` joins as `rho^j` times
itself, its slices and its pieces' scales, the pieces grouped by point in first-seen order; the
target `T = Σ_i x^i Φ(s_i)` of the merged slices, and the weight `ringWeight` of the groups under
the map's Frobenius coefficients. -/
def ringMerge (claims : List RingClaim) (f g : List E) (rho : E) : StackClaim :=
  let merged := claims.foldl (fun (acc : List E × List RingPointGroup × List (List E) × E) claim ↦
    let (slices, groups, points, rhoJ) := acc
    let slices := slices.zipIdx.map fun (sum, i) ↦
      match claim.slices[i]? with
      | some s => sum + rhoJ * s
      | none => sum
    let (groups, points) := claim.pieces.foldl (fun (gp : List RingPointGroup × List (List E))
        piece ↦
      let (groups, points) := gp
      let scale := frobenius (rhoJ * piece.scale)
      match points.findIdx? (fun p ↦ decide (p = piece.point)) with
      | some index => (groups.modify index fun group ↦
          { group with pieces := group.pieces ++ [(piece.placement, scale)] }, points)
      | none => (groups ++ [⟨piece.point.map frobenius, [(piece.placement, scale)]⟩],
          points ++ [piece.point])) (groups, points)
    (slices, groups, points, rhoJ * rho)) (List.replicate kBits 0, [], [], 1)
  let coefficients := ringCoefficients f g
  (fun x ↦ ringWeight merged.2.1 x coefficients, ringTarget merged.1 f g)

/-- `ring_switch(claims, transcript)` (`ring_switch.rs`): the claims' 64 slices become one dense
claim `Σ_u W(u) column(u) = T` on the stack. One grind (`BATCH_GRINDING_BITS`) covers one packed
draw: the map's sixteen challenges, `f` then `g`, then `rho` when there are several claims (`1`
otherwise), then the stacked opening's batching challenge, which it returns with the claim. -/
def ringSwitch (claims : List RingClaim) : VerifierProgram (StackClaim × E) := do
  VerifierProgram.grindProofOfWork Whir.batchGrindingBits
  let merging := decide (1 < claims.length)
  let challenges ← VerifierProgram.sampleChallengesPacked
    (2 * ringMapWidth + (if merging then 1 else 0) + 1)
  let f := challenges.take ringMapWidth
  let g := (challenges.drop ringMapWidth).take ringMapWidth
  let rest := challenges.drop (2 * ringMapWidth)
  let (rho, batching) := if merging then (rest.getD 0 0, rest.getD 1 0) else (1, rest.getD 0 0)
  return (ringMerge claims f g rho, batching)

end LeanVM.Protocol.Verifier

end
