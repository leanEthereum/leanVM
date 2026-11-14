module

public import Statement.Prover.Script

/-!
# The additive NTT and the committed words

The encoder of leanVM's binary Reed-Solomon code in the novel basis (Annex D,
`doc/leanvm/body/d-novel-basis.tex`: `Enc(g)(x_p) = Σ_u g(u)·X_⟨u⟩(x_p)`,
`X_j = ∏_i Ŵ_i^{j_i}`, `Ŵ_i` the normalized subspace polynomials, `x_p = K.ofBits p`) for all
`2^(κ+R)` domain points at once, in `O((κ+R)·2^(κ+R))` operations
(`AdditiveNttF64`, `crates/pcs/src/ntt/twiddles.rs`, and its `standard`).
`Ŵ_i(x_p)` depends only on `p >>> i` (`Ŵ_i` is additive and vanishes on `U_i`), so the transform
folds the message's variables from the top, a stage the butterfly
`(u, v) ↦ (u + t·v, u + (t + 1)·v)` with the twiddle `t = Ŵ_i(x_{b·2^(i+1)})` of the block `b`;
the twiddles come by additivity from the table of `Ŵ_c(e_m)`, `c, m < 64`.

A committed word's leaf `p` reads the codewords at `p`; a run reads the leaves below the committed
height `2^(κ+R)` only.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## The subspace polynomials on the basis -/

/-- Row `c` of the subspace polynomials on the basis, `W_c(e_m)` for `m < 64`: `W_0(a) = a`,
`W_{c+1}(a) = W_c(a)^2 + W_c(e_c)·W_c(a)`. -/
def vanRow : ℕ → Array K
  | 0 => Array.ofFn (n := 64) fun m ↦ K.ofBits (2 ^ m.val)
  | c + 1 =>
    let r := vanRow c
    let root := r.getD c 0
    r.map fun v ↦ v * v + root * v

/-- Row `c` of the normalized subspace polynomials on the basis, `Ŵ_c(e_m)` for `m < 64`. -/
def hatRow (c : ℕ) : Array K :=
  let r := vanRow c
  let inv := (r.getD c 0)⁻¹
  r.map (· * inv)

/-- The table of `Ŵ_c(e_m)`, `c, m < 64`. -/
def hatTable : Array (Array K) := Array.ofFn (n := 64) fun c ↦ hatRow c

/-- `Ŵ_c(x_n)` for `c < 64`: `Ŵ_c` is additive and `x_n = Σ_{m < 64} n_m e_m`. -/
def hatAt (c n : ℕ) : K :=
  let row := hatTable.getD c #[]
  (List.range 64).foldl (fun acc m ↦ if n.testBit m then acc + row.getD m 0 else acc) 0

/-! ## The transform -/

/-- The twiddles of stage `i` of a transform on `2^N` positions: `Ŵ_i(x_{b·2^(i+1)})` for the
block `b < 2^(N-i-1)` of `2^(i+1)` positions. -/
def stageTwiddles (N i : ℕ) : Array K :=
  Array.ofFn (n := 2 ^ (N - (i + 1))) fun b ↦ hatAt i (b.val * 2 ^ (i + 1))

/-- The twiddles of the stages `i < κ` of a transform on `2^N` positions. -/
def nttTwiddles (N κ : ℕ) : Array (Array K) := Array.ofFn (n := κ) fun i ↦ stageTwiddles N i.val

/-- Stage `i` of the transform on `2^N` positions, with the stage's twiddles `tw`: in the block
`b` the pair `(u, v)` at `lo = b·2^(i+1) + j` and `lo + 2^i` (`j < 2^i`) becomes
`(u + t·v, u + t·v + v)`, `t = tw[b]`. The products `t·v` are computed once per pair. -/
def nttStage (N i : ℕ) (tw : Array K) (a : Array K) : Array K :=
  nttStageAt N (2 ^ i) (2 ^ (i + 1)) tw a
where
  /-- The stage with `2^i` and `2^(i+1)` computed once (`pi`, `pi1`). -/
  nttStageAt (N pi pi1 : ℕ) (tw : Array K) (a : Array K) : Array K :=
    let half : Array K := Array.ofFn (n := 2 ^ (N - 1)) fun q ↦
      let b := q.val / pi
      tw.getD b 0 * a.getD (b * pi1 + pi + q.val % pi) 0
    Array.ofFn (n := 2 ^ N) fun p ↦
      let b := p.val / pi1
      let r := p.val % pi1
      let j := r % pi
      let lo := b * pi1 + j
      let u := a.getD lo 0 + half.getD (b * pi + j) 0
      if r < pi then u else u + a.getD (lo + pi) 0

/-- **The additive NTT** of a message of `2^κ` entries on `2^(κ+R)` positions, with the twiddles
`tws = nttTwiddles (κ + R) κ`: the message repeated `2^R` times, then the stages
`κ - 1, …, 0`. -/
def ntt (tws : Array (Array K)) (κ R : ℕ) (msg : Array K) : Array K :=
  go κ (Array.ofFn (n := 2 ^ (κ + R)) fun p ↦ msg.getD (p.val % 2 ^ κ) 0)
where
  /-- The stages `i - 1, …, 0`. -/
  go : ℕ → Array K → Array K
    | 0, a => a
    | i + 1, a => go i (nttStage (κ + R) i (tws.getD i #[]) a)

/-! ## The committed words -/

/-- The codewords of the stack's 64 lanes: lane `u` encodes the block of `2^(μ-6)` cells at
`u·2^(μ-6)`. -/
def stackCodes (μ R : ℕ) (stack : Array K) : Array (Array K) :=
  let κ := μ - 6
  let tws := nttTwiddles (κ + R) κ
  Array.ofFn (n := 64) fun u ↦
    ntt tws κ R (Array.ofFn (n := 2 ^ κ) fun v ↦ stack.getD (v.val + 2 ^ κ * u.val) 0)

/-- **The stack's level-0 word**: leaf `p` holds the 64 lanes' codeword entries at `x_p`, in
reverse lane order. -/
@[macro_inline] def stackWordFast (μ R : ℕ) (stack : Array K) : Word :=
  stackWordOf (stackCodes μ R stack)
where
  /-- The word from the lanes' codewords `codes`, computed once: the word is a closure over
  them (`stackWordFast` is inlined where it is used, so that `codes` is evaluated before the
  closure is formed). -/
  stackWordOf (codes : Array (Array K)) (p : ℕ) : List K :=
    ((List.range 64).map fun u ↦ (codes.getD u #[]).getD p 0).reverse

/-- The codewords of a level's lanes, limb by limb: entry `2j + l` encodes limb `l` of the lane
`j`, `x ↦ g[j + 2^k·x]`. -/
def levelCodes (κ k R : ℕ) (g : Array E) : Array (Array K) :=
  let tws := nttTwiddles (κ + R) κ
  Array.ofFn (n := 2 * 2 ^ k) fun jl ↦
    ntt tws κ R (Array.ofFn (n := 2 ^ κ) fun v ↦
      (g.getD (jl.val / 2 + 2 ^ k * v.val) 0).limb ⟨jl.val % 2, Nat.mod_lt _ (by decide)⟩)

/-- **A deeper level's word**: leaf `p` holds the `2^k` lanes' entries at `x_p`, two limbs
each. -/
@[macro_inline] def levelWordFast (κ k R : ℕ) (g : Array E) : Word :=
  levelWordOf k (levelCodes κ k R g)
where
  /-- The word from the lanes' codewords `codes`, computed once (as for `stackWordFast`). -/
  levelWordOf (k : ℕ) (codes : Array (Array K)) (p : ℕ) : List K :=
    (List.range (2 ^ k)).flatMap fun j ↦
      [(codes.getD (2 * j) #[]).getD p 0, (codes.getD (2 * j + 1) #[]).getD p 0]

end LeanVM.Prover

end
