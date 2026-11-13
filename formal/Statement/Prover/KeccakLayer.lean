module

public import Statement.Prover.KeccakTables

/-!
# The Keccak prover: a layer

One layer of the Keccak GKR (`verifyKeccakLayer`; `verify_layer`,
`crates/verifier/src/keccak.rs:116-196`): the bits entering χ, the sixteen instances of a pack as a
mask per position (`layerMasks`); `G`'s coefficients, χ's product of the embedded masks as a
carry-less product (`gCoeffs`); the pack rounds and the position rounds on tables folded in place;
the next claim through `keccakLinearTranspose`.
-/

@[expose] public section

namespace LeanVM.Prover.KeccakGkr

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-! ## The states -/

/-- Segment `m`'s committed input at step `x` (slots `25m .. 25m + 24` of `2^h` words). -/
def inStateOf (col : ℕ → K) (h m x : ℕ) : KeccakState :=
  Vector.ofFn fun l : Fin 25 ↦ K.lane (col (x + 2 ^ h * (25 * m + l)))

/-- `e` rounds of `keccakF1600` from round `start`. -/
def roundsOf (start e : ℕ) (a : KeccakState) : KeccakState :=
  ((keccakRC.drop start).take e).foldl Keccak.round a

/-- The linear map of a round on lanes: θ, then ρ and π. -/
def linearOf (a : KeccakState) : KeccakState :=
  let c : Vector UInt64 5 := Vector.ofFn fun x ↦
    Keccak.lane a x ^^^ Keccak.lane a (x + 5) ^^^ Keccak.lane a (x + 10) ^^^
      Keccak.lane a (x + 15) ^^^ Keccak.lane a (x + 20)
  let t : KeccakState := Vector.ofFn fun i ↦
    Keccak.lane a i ^^^ c.toArray.getD ((i.val + 4) % 5) 0 ^^^
      Keccak.rot (c.toArray.getD ((i.val + 1) % 5) 0) 1
  (List.range 25).foldl
    (fun b i ↦ b.setIfInBounds (keccakPi i) (Keccak.rot (Keccak.lane t i) (keccakRho.getD i 0)))
    (Vector.replicate 25 0)

/-- Bit `j = z + 64ℓ` of a state: bit `z` of lane `ℓ`. -/
def bitOf (a : KeccakState) (j : ℕ) : Bool := (Keccak.lane a (j / 64)).toBitVec.getLsbD (j % 64)

/-- The bits entering χ in pack `z` (segment `z / 2^P`, steps `16·(z mod 2^P) + i`), `e` rounds
into the segment: per position `j`, the sixteen instances' bits as a mask. -/
def packMasks (col : ℕ → K) (P e z : ℕ) : Array ℕ :=
  let m := z / 2 ^ P
  let ls : Array KeccakState := Array.ofFn (n := 16) fun i ↦
    linearOf (roundsOf (12 * m) e (inStateOf col (P + 4) m (i.val + 16 * (z % 2 ^ P))))
  Array.ofFn (n := 1600) fun j ↦ packBits (fun i ↦ bitOf (ls.getD i default) j.val) 16

/-- The masks of every pack. -/
def layerMasks (col : ℕ → K) (P e : ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := 2 ^ (P + 1)) fun z ↦ packMasks col P e z.val

/-! ## The product polynomial -/

/-- The embedding of the bits of a byte as instances `off .. off + 7`: the sum of their
embeddings. -/
def embedByte (off b : ℕ) : ℕ :=
  (List.range 8).foldl (fun acc t ↦ if b.testBit t then acc ^^^ rmfeEmbed.getD (off + t) 0 else acc)
    0

/-- `embedByte 0` on every byte. -/
def embedLow : Array ℕ := Array.ofFn (n := 256) fun b ↦ embedByte 0 b.val

/-- `embedByte 8` on every byte. -/
def embedHigh : Array ℕ := Array.ofFn (n := 256) fun b ↦ embedByte 8 b.val

/-- The embedding of a mask of sixteen instances, a binary polynomial of degree below `24`:
`Σ_{i ∈ mask} emb_i`. -/
def embedMask (mask : ℕ) : ℕ :=
  embedLow.getD (mask % 256) 0 ^^^ embedHigh.getD (mask / 256 % 256) 0

/-- `κ = emb(1, …, 1)`. -/
def kappaBits : ℕ := embedMask 0xFFFF

/-- The carry-less product of the low `k` bits of `a` and `b`. -/
def clmul : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b => (if a % 2 = 1 then b else 0) ^^^ (clmul k (a / 2) b <<< 1)

/-- χ's product at a position, `κ·S_j + (κ + S_{j+1})·S_{j+2}`, of the embedded masks
`S_j, S_{j+1}, S_{j+2}`. -/
def chiProduct (s0 s1 s2 : ℕ) : ℕ := clmul 24 kappaBits s0 ^^^ clmul 24 (kappaBits ^^^ s1) s2

/-- The byte tables of the position weights, eight positions each: table `q` of
`w_{8q}, …, w_{8q+7}`. -/
def weightTabs (w : Array E) : Array (Array E) :=
  Array.ofFn (n := 200) fun q ↦ byteSums fun t ↦ w.getD (8 * q.val + t) 0

/-- A pack's share of `G`, its embedded masks `S`: coefficient `c` is
`Σ_j w_j·[bit c of χ's product at j]`, eight positions per read of the weights' byte tables
`wT`. -/
def gPack (wT : Array (Array E)) (S : Array ℕ) : Array E :=
  let g : Array ℕ := Array.ofFn (n := 1600) fun j ↦
    chiProduct (S.getD j.val 0) (S.getD (keccakAlong j.val 1) 0) (S.getD (keccakAlong j.val 2) 0)
  Array.ofFn (n := 47) fun c ↦ sumRange 200 fun q ↦
    (wT.getD q #[]).getD (packBits (fun t ↦ (g.getD (8 * q + t) 0).testBit c.val) 8) 0

/-- **`G`'s coefficients**: `Σ_z eq(point, z)·gPack z`. -/
def gCoeffs (P : ℕ) (masks : Array (Array ℕ)) (point w : List E) : List E :=
  let eq := eqTable point
  let wT := weightTabs w.toArray
  let G := (List.range (2 ^ (P + 1))).foldl (fun G z ↦
    let gz := gPack wT ((masks.getD z #[]).map embedMask)
    let e := eq.getD z 0
    Array.ofFn (n := 47) fun c ↦ G.getD c.val 0 + e * gz.getD c.val 0) (Array.replicate 47 0)
  (List.range 47).map fun c ↦ G.getD c 0

/-! ## The pack and segment rounds -/

/-- The packs' state entering χ at `s` at pack `z` and position `j`,
`Σ_i μ_i·[bit i of the mask]`, by two byte tables (`lo` of `μ_0 .. μ_7`, `hi` of
`μ_8 .. μ_15`). -/
def shatAt (lo hi : Array E) (masks : Array (Array ℕ)) (z j : ℕ) : E :=
  let m := (masks.getD z #[]).getD j 0
  lo.getD (m % 256) 0 + hi.getD (m / 256 % 256) 0

/-- The pack rounds' state: the table of the packs' states at the challenges so far (entry
`(z, j)`), the product of the scales, and the claim's point's coordinates still to come. -/
structure PackState where
  get : ℕ → ℕ → E
  scale : E
  rest : List E

/-- The state before the pack rounds, at the claim's point `point`. -/
def packStart (masks : Array (Array ℕ)) (mu point : List E) : PackState :=
  let μ := mu.toArray
  let lo := byteSums fun t ↦ μ.getD t 0
  let hi := byteSums fun t ↦ μ.getD (8 + t) 0
  ⟨shatAt lo hi masks, 1, point⟩

/-- The coefficients of `x ↦ w·(κ·S_0(x) + (κ + S_1(x))·S_2(x))`, `S_k(x) = l_k + x·d_k`. -/
def chiCoeffs (κ w l0 d0 l1 d1 l2 d2 : E) : List E :=
  let k1 := κ + l1
  [w * (κ * l0 + k1 * l2), w * (κ * d0 + d1 * l2 + k1 * d2), w * (d1 * d2)]

/-- **A pack round's polynomial**: `scale · Σ_z eq(rest, z) Σ_j w_j·χ` at the next coordinate
`x`, each pack row affine in `x` between the rows `2z` and `2z + 1`. -/
def packRound (κ : E) (w : Array E) (st : PackState) : List E :=
  let eq := eqTable st.rest.tail
  scaleCoeffs st.scale <| sumCoeffs 3 (2 ^ (st.rest.length - 1)) fun z ↦
    let lo : Array E := Array.ofFn (n := 1600) fun j ↦ st.get (2 * z) j.val
    let d : Array E := Array.ofFn (n := 1600) fun j ↦ lo.getD j.val 0 + st.get (2 * z + 1) j.val
    scaleCoeffs (eq.getD z 0) <| sumCoeffs 3 1600 fun j ↦
      chiCoeffs κ (w.getD j 0) (lo.getD j 0) (d.getD j 0) (lo.getD (keccakAlong j 1) 0)
        (d.getD (keccakAlong j 1) 0) (lo.getD (keccakAlong j 2) 0) (d.getD (keccakAlong j 2) 0)

/-- **A pack round's fold** at the challenge `c`: the rows `2z, 2z + 1` become row `z`, the scale
gains `1 + r + c`. -/
def packFold (st : PackState) (c : E) : PackState :=
  let T : Array (Array E) := Array.ofFn (n := 2 ^ (st.rest.length - 1)) fun z ↦
    Array.ofFn (n := 1600) fun j ↦
      let lo := st.get (2 * z.val) j.val
      lo + c * (lo + st.get (2 * z.val + 1) j.val)
  ⟨fun z j ↦ (T.getD z #[]).getD j 0, st.scale * (1 + st.rest.headD 0 + c), st.rest.tail⟩

/-! ## The position rounds -/

/-- The position rounds' tables over the `11` position bits. -/
structure PosState where
  t0 : Array E
  t1 : Array E
  t2 : Array E
  wt : Array E

/-- The tables before the position rounds: the packs' states at the pack point (`row`), at `j`
and `1`, `2` columns along, and the position weights, zero past `1600`. -/
def posStart (row : ℕ → E) (w : Array E) : PosState :=
  ⟨Array.ofFn (n := 2048) fun u ↦ if u.val < 1600 then row u.val else 0,
    Array.ofFn (n := 2048) fun u ↦ if u.val < 1600 then row (keccakAlong u.val 1) else 0,
    Array.ofFn (n := 2048) fun u ↦ if u.val < 1600 then row (keccakAlong u.val 2) else 0,
    Array.ofFn (n := 2048) fun u ↦ if u.val < 1600 then w.getD u.val 0 else 0⟩

/-- The coefficients of `x ↦ W(x)·(κ·T_0(x) + (κ + T_1(x))·T_2(x))`, `W(x) = wl + x·wd`,
`T_k(x) = l_k + x·d_k`. -/
def posCoeffs (κ wl wd l0 d0 l1 d1 l2 d2 : E) : List E :=
  let k1 := κ + l1
  let q0 := κ * l0 + k1 * l2
  let q1 := κ * d0 + d1 * l2 + k1 * d2
  let q2 := d1 * d2
  [wl * q0, wl * q1 + wd * q0, wl * q2 + wd * q1, wd * q2]

/-- **A position round's polynomial**: `scale · Σ_u W·(κ·T_0 + (κ + T_1)·T_2)` at the next
coordinate. -/
def posRound (κ scale : E) (st : PosState) : List E :=
  scaleCoeffs scale <| sumCoeffs 4 (st.t0.size / 2) fun u ↦
    posCoeffs κ (st.wt.getD (2 * u) 0) (st.wt.getD (2 * u) 0 + st.wt.getD (2 * u + 1) 0)
      (st.t0.getD (2 * u) 0) (st.t0.getD (2 * u) 0 + st.t0.getD (2 * u + 1) 0)
      (st.t1.getD (2 * u) 0) (st.t1.getD (2 * u) 0 + st.t1.getD (2 * u + 1) 0)
      (st.t2.getD (2 * u) 0) (st.t2.getD (2 * u) 0 + st.t2.getD (2 * u + 1) 0)

/-- A position round's fold. -/
def posFold (st : PosState) (c : E) : PosState :=
  ⟨foldPairsA c st.t0, foldPairsA c st.t1, foldPairsA c st.t2, foldPairsA c st.wt⟩

/-! ## A layer -/

/-- The verifier's batched weights (`keccak.rs:188-193`) from an equality table. -/
def batchWeights (p : List E) (beta : E) : List E :=
  let e := eqTable p
  (List.range keccakBits).map fun j ↦
    e.getD j 0 + beta * (e.getD (keccakAlong j 4) 0 + beta * e.getD (keccakAlong j 3) 0)

/-- **The honest prover of layer `d`** on the column `col` (the states `11 - d` rounds into each
segment), from `claim`: `G`'s coefficients, a grind and `s`, the pack rounds, the position
rounds, `t`, a grind and `β`, and the next claim. -/
def layerProve (col : ℕ → K) (P d : ℕ) (claim : KeccakClaim) : Script KeccakClaim :=
  let masks := layerMasks col P (11 - d)
  (Script.sendList (gCoeffs P masks claim.point claim.weights)).bind fun _ ↦
  (Script.grindBits (grindingBits (productBits - 1))).bind fun _ ↦
  Script.sampleE.bind fun s ↦
  let mu := keccakInstanceWeights s
  let κ := sumE mu
  let w := claim.weights.toArray
  (sumcheckBy (packRound κ w) packFold (claim.point.map some)
      (packStart masks mu claim.point)).bind fun pk ↦
  (sumcheckBy (posRound κ pk.2.scale) posFold (List.replicate keccakLocalBits none)
      (posStart (pk.2.get 0) w)).bind fun ps ↦
  let t0 := ps.2.t0.getD 0 0
  let t1 := ps.2.t1.getD 0 0
  let t2 := ps.2.t2.getD 0 0
  (Script.sendList [t0, t1, t2]).bind fun _ ↦
  (Script.grindBits (grindingBits 2)).bind fun _ ↦
  Script.sampleE.bind fun b ↦
  Script.ret ⟨t0 + b * (t1 + b * t2), mu, pk.1, keccakLinearTranspose (batchWeights ps.1 b)⟩

/-- The honest layers `ds`. -/
def layersProve (col : ℕ → K) (P : ℕ) : List ℕ → KeccakClaim → Script KeccakClaim
  | [], claim => .ret claim
  | d :: ds, claim => (layerProve col P d claim).bind fun c ↦ layersProve col P ds c

end LeanVM.Prover.KeccakGkr

end
