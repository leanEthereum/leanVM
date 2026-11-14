module

public import Statement.Prover.Ntt
public import Statement.Prover.Mle

/-!
# Ring switching and the WHIR opening

The honest prover of ring switching (`ringSwitch`: `ring_switch`,
`crates/verifier/src/ring_switch.rs:70-87`) and of the stacked opening (`verifyStackedOpening`:
`verify_stacked_opening`, `crates/verifier/src/lib.rs:133-154`, then `verify_whir`,
`crates/verifier/src/whir.rs:215-329`), the prover's side being `recursive_prover_with_prepared_basis`
(`crates/pcs/src/whir.rs:739-935`), on arrays.

The claims are descriptions (`ClaimDesc`) whose denotations are the verifier's stack claims; their
weights are closures the prover does not evaluate on the cube: the starting weight table is built
by scatter, a column claim's equality kernel on its block of the stack and the ring claim's `Φ` of
the equality kernel on `q_keccak`'s block (`basisTableA`). The lanes are tables of novel-basis
coefficients, coefficient `c` of lane `l` at `c·stride + l` (the Rust's `Dense`): a fold round
sends the table of the half `F` and of `X F` against the weight (`mulXA`, `roundTableA`) and folds
the lanes to `G + α F + β X F`, one coefficient longer, and the weight by the same `α`. A level's
word is the additive NTT of the folded lane's low part (`levelWordFast`), its query table the
queries' tensor products `∏_c (1, Ŵ_c(x_q))` summed (`queryTableA`). The prover's messages do not
depend on the running claim, which it does not track.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-! ## Ring switching -/

/-- What ring switching leaves for the opening: the target `Σ_i x^i Φ(s_i)`, the Keccak
reduction's point on `q_keccak`, and the map's challenges `f` and `g`. -/
structure RingOut where
  target : E
  point : List E
  f : List E
  g : List E

/-- **The honest prover of ring switching** (`ring_switch`,
`crates/verifier/src/ring_switch.rs:70-87`; the prover's `sample_map_challenges`,
`crates/pcs/src/ring_switch.rs:149-151`): it sends nothing; a grind, then the sixteen challenges,
`f` then `g`; the target with the point and the challenges. -/
def ringFast (point slices : List E) : Script RingOut := do
  Script.grindBits Whir.batchGrindingBits
  let challenges ← Script.sampleN (2 * ringMapWidth)
  let f := challenges.take ringMapWidth
  let g := challenges.drop ringMapWidth
  return ⟨ringTarget slices f g, point, f, g⟩

/-- `Φ(value) = Σ_p f_p Ψ(value)^(2^(8p))`, `Ψ(v) = Σ_b g_b v^(2^b)`, stage by stage, by squarings
(`apply_map`, `crates/pcs/src/ring_switch.rs:129-145`). -/
def ringPhi (f g : List E) (value : E) : E :=
  (f.foldl (fun (acc : E × E) fP ↦
    (acc.1 + fP * acc.2, Nat.repeat (fun v ↦ v * v) ringMapWidth acc.2)) (0, ringPsi value g)).1

/-! ## The claims -/

/-- A claim on the stack, as the opening receives it. -/
inductive ClaimDesc where
  /-- The ring-switching claim: its target, the Keccak reduction's point and the map's
  challenges `f`, `g`. -/
  | ring (layout : Layout) (target : E) (point f g : List E)
  /-- A column claim. -/
  | column (layout : Layout) (claim : ColumnClaim)
  /-- The stack commitment's out-of-domain claim: the stack's multilinear at `z` is `value`. -/
  | ood (z : List E) (value : E)

/-- **The stack claim a description stands for**: the ring-switching claim with the weight
`ringWeight point · (ringCoefficients f g)`, the column claim on the stack, or the out-of-domain
claim. -/
def ClaimDesc.denote : ClaimDesc → StackClaim
  | .ring layout target point f g =>
    ringSwitchClaim layout target fun rPrime ↦ ringWeight point rPrime (ringCoefficients f g)
  | .column layout c =>
    (fun x ↦ eqEval ((layout.placement c.column).stackPoint c.point layout.stackLog) x, c.value)
  | .ood z value => (fun x ↦ eqEval z x, value)

/-- The ring-switching claim of ring switching's result. -/
def RingOut.claim (r : RingOut) (layout : Layout) : ClaimDesc :=
  .ring layout r.target r.point r.f r.g

/-! ## Tables -/

/-- The constant coefficient `Σ_x W(0,x)·g(0,x)` of a tail round's polynomial (`roundC0`). -/
def roundC0A (W g : Array E) : E :=
  sumRange (min W.size g.size / 2) fun x ↦ W.getD (2 * x) 0 * g.getD (2 * x) 0

/-- The quadratic coefficient `Σ_x (W(0,x) + W(1,x))·(g(0,x) + g(1,x))` (`roundC2`). -/
def roundC2A (W g : Array E) : E :=
  sumRange (min W.size g.size / 2) fun x ↦
    (W.getD (2 * x) 0 + W.getD (2 * x + 1) 0) * (g.getD (2 * x) 0 + g.getD (2 * x + 1) 0)

/-- Gluing the claims' tables into the weight table, `W + Σ_k λ^(k+1)·T_k` (`glueTables`). -/
def glueTablesA (lam : E) (W : Array E) (Ts : List (Array E)) : Array E :=
  (Ts.foldl (fun (acc : Array E × E) T ↦
    let s := acc.2 * lam
    (Array.zipWith (fun a b ↦ a + s * b) acc.1 T, s)) (W, 1)).1

/-- The tensor product `⊗_c (1, w_c)`: entry `i` is `∏_{c : i_c} w_c`, bit `0` first. -/
def tensorA (ws : List K) : Array K := ws.foldl (fun v w ↦ v ++ v.map (· * w)) #[1]

/-- A level's query table (`queryTable`): entry `i < 2^m` is `Σ_q w_q·X_i(x_q)`, the tensor
products of `(1, Ŵ_c(x_q))`, `c < m`, summed with the weights. -/
def queryTableA (m : ℕ) (queries : List ℕ) (queryWeights : List E) : Array E :=
  (List.zip queryWeights queries).foldl (fun acc wq ↦
      let t := tensorA ((List.range m).map fun c ↦ hatAt c wq.2)
      Array.zipWith (fun a b ↦ a + wq.1 * ofK b) acc t)
    (Array.replicate (2 ^ m) 0)

/-! ## The starting claim -/

/-- The cube point of `y` on `m` coordinates, bit `0` first (`boolPoint`). -/
def cubePoint (m y : ℕ) : List E := (List.range m).map fun i ↦ if y.testBit i then 1 else 0

/-- The block of `2^v` positions a placement at `index` selects on a cube of `2^μ` positions: its
first position. -/
def blockOff (μ v index : ℕ) : ℕ := index / 2 ^ v % 2 ^ (μ - v) * 2 ^ v

/-- Add `s·vals[j]` at the positions `off + j`, `j < n`, in place. -/
def addSlice (off : ℕ) (vals : Array E) (s : E) : ℕ → Array E → Array E
  | 0, acc => acc
  | n + 1, acc => addSlice off vals s n (acc.modify (off + n) (· + s * vals.getD n 0))

/-- Add `s·w(y)` at every position `y` (the weight's formula; a claim of no other shape). -/
def addFull (μ : ℕ) (w : List E → E) (s : E) (acc : Array E) : Array E :=
  Array.ofFn (n := acc.size) fun y ↦ acc.getD y.val 0 + s * w (cubePoint μ y.val)

/-- Add `s` times a claim's weight on the cube of `2^μ` positions, in the stack's order: a column
claim's equality kernel on its block, the ring claim's `Φ ∘ eq` on the block of `q_keccak`, the
out-of-domain claim's equality kernel on the whole stack. -/
def addClaim (μ : ℕ) (acc : Array E) (s : E) (d : ClaimDesc) : Array E :=
  match d with
  | .column layout c =>
    let pl := layout.placement c.column
    if c.point.length = pl.variableCount ∧ pl.variableCount ≤ μ ∧ layout.stackLog = μ then
      let vals := eqTable c.point
      addSlice (blockOff μ pl.variableCount pl.index) vals s vals.size acc
    else addFull μ d.denote.1 s acc
  | .ring layout _ point f g =>
    let pl := layout.placement qkeccak
    if point.length = pl.variableCount ∧ pl.variableCount ≤ μ ∧ f.length = ringMapWidth ∧
        g.length = ringMapWidth then
      let vals := (eqTable point).map (ringPhi f g)
      addSlice (blockOff μ pl.variableCount pl.index) vals s vals.size acc
    else addFull μ d.denote.1 s acc
  | .ood z _ =>
    if z.length = μ then
      let vals := eqTable z
      addSlice 0 vals s vals.size acc
    else addFull μ d.denote.1 s acc

/-- The batched weight `Σ_k s_k·w_k` on the cube, in the stack's order. -/
def basisNat (μ : ℕ) (scales : List E) (claims : List ClaimDesc) : Array E :=
  (List.zip scales claims).foldl (fun acc sd ↦ addClaim μ acc sd.1 sd.2)
    (Array.replicate (2 ^ μ) 0)

/-- **The weight table of the starting claim** (`basisTable`): the batched weight at the rotated
cube point, entry `i` at the stack position `⌊i / 64⌋ + 2^(μ-6)·(i mod 64)`. -/
def basisTableA (μ : ℕ) (scales : List E) (claims : List ClaimDesc) : Array E :=
  if 6 ≤ μ then
    let N := basisNat μ scales claims
    Array.ofFn (n := 2 ^ μ) fun i ↦ N.getD (i.val / 2 ^ 6 + 2 ^ (μ - 6) * (i.val % 2 ^ 6)) 0
  else
    Array.ofFn (n := 2 ^ μ) fun i ↦
      dot scales (claims.map fun c ↦
        c.denote.1 ((cubePoint μ i.val).drop 6 ++ (cubePoint μ i.val).take 6))

/-- The stack in the WHIR variable order (`stackTable`): entry `i` is the cell
`⌊i / 64⌋ + 2^(μ-6)·(i mod 64)`. -/
def stackTableA (μ : ℕ) (stack : Array K) : Array E :=
  Array.ofFn (n := 2 ^ μ) fun i ↦
    ofK (stack.getD (i.val / 2 ^ 6 + 2 ^ (μ - 6) * (i.val % 2 ^ 6)) 0)

/-! ## Multiplication by `X` in the novel basis -/

/-- `W_t(β_t)`, `t < 64`: the normalizer of `Ŵ_t` (`eval_sk_at_vks`,
`crates/pcs/src/whir_induce.rs`). -/
def subspaceRoot (t : ℕ) : K := (vanRow t).getD t 0

/-- `A_t = a_0 ⋯ a_(t-1)`, `a_i = W_(i+1)(β_(i+1)) / W_i(β_i)^2`, for `t < 64`: `X_c` times `X` has the
coefficient `A_t` on the two basis elements it reaches, `t` the trailing zeros of `c`
(`constants`, `crates/pcs/src/xmul.rs:52-63`). -/
def xmulConsts : Array K :=
  (List.range 63).foldl (fun a t ↦
    a.push (a.getD t 1 * subspaceRoot (t + 1) * (subspaceRoot t * subspaceRoot t)⁻¹)) #[1]

/-- The trailing zeros of `c ≥ 1`: `c xor (c - 1) = 2^(t+1) - 1`. -/
def trailingZeros (c : ℕ) : ℕ := Nat.log2 (c ^^^ (c - 1))

/-- **`X` times every lane** of a table of `stride` lanes, coefficient `c` of lane `l` at
`c·stride + l`, one coefficient longer: `(X h)[0] = 0`,
`(X h)[c] = A_t (h[c - 1] + h[c + 2^t - 1])`, `t` the trailing zeros of `c`, zero past `h`
(`mul_x`, `crates/pcs/src/xmul.rs:71-92`; Annex D, Lemma `lem:mulx`). -/
def mulXA (h : Array E) (stride : ℕ) : Array E :=
  Array.ofFn (n := (h.size / stride + 1) * stride) fun i ↦
    let c := i.val / stride
    let l := i.val % stride
    if c = 0 then 0
    else
      let t := trailingZeros c
      ofK (xmulConsts.getD t 0) * (h.getD ((c - 1) * stride + l) 0 +
        h.getD ((c + 2 ^ t - 1) * stride + l) 0)

/-! ## The fold rounds -/

/-- `Σ_i a_i b_i` over the shorter array. -/
def dotA (a b : Array E) : E := sumRange (min a.size b.size) fun i ↦ a.getD i 0 * b.getD i 0

/-- The half `F` of a table `f` of `s` lanes, coefficient by coefficient (`Dense::table`,
`crates/pcs/src/whir.rs:573-607`): `F`, `G` the lanes `2m`, `2m + 1`. -/
def halfA (f : Array E) (s : ℕ) : Array E :=
  Array.ofFn (n := f.size / s * (s / 2)) fun i ↦
    f.getD (i.val / (s / 2) * s + 2 * (i.val % (s / 2))) 0

/-- **A fold round's table** `[u₀, w, c₀, c₁] = [⟨W₀, G⟩, ⟨W₀ + W₁, F⟩, ⟨W₀, XF⟩, ⟨W₁, XF⟩]`
over the low coefficients the weight `w` covers, from the halves' table `f`, `H = F` and
`XH = X F`. -/
def roundTableA (f w : Array E) (s : ℕ) (H XH : Array E) : List E :=
  let n := w.size / s * (s / 2)
  let at_ := fun i ↦ (i / (s / 2)) * s + 2 * (i % (s / 2))
  [sumRange n fun i ↦ w.getD (at_ i) 0 * f.getD (at_ i + 1) 0,
   sumRange n fun i ↦ (w.getD (at_ i) 0 + w.getD (at_ i + 1) 0) * H.getD i 0,
   sumRange n fun i ↦ w.getD (at_ i) 0 * XH.getD i 0,
   sumRange n fun i ↦ w.getD (at_ i + 1) 0 * XH.getD i 0]

/-- The folded lanes `P = G + α F + β X F`, one coefficient longer (`Dense::fold`,
`crates/pcs/src/whir.rs:610-647`). -/
def foldLanesA (f : Array E) (s : ℕ) (H XH : Array E) (α β : E) : Array E :=
  Array.ofFn (n := XH.size) fun i ↦
    let c := i.val / (s / 2)
    let m := i.val % (s / 2)
    f.getD (c * s + 2 * m + 1) 0 + α * H.getD i.val 0 + β * XH.getD i.val 0

/-- **One fold round** (`fold_round`, `crates/pcs/src/whir.rs:533-539`): the table, a grind and
`(α, β)`; the folded lanes and the weight folded by `α`. -/
def foldRoundA (f w : Array E) (s : ℕ) : Script (Array E × Array E) := do
  let H := halfA f s
  let XH := mulXA H (s / 2)
  Script.sendList (roundTableA f w s H XH)
  Script.grindBits Whir.foldGrindingBits
  let α ← Script.sampleE
  let β ← Script.sampleE
  return (foldLanesA f s H XH α β, foldPairsA α w)

/-- A level's fold rounds, the lanes halving each round. -/
def foldRoundsA : ℕ → ℕ → Array E → Array E → Script (Array E × Array E)
  | 0, _, f, w => return (f, w)
  | n + 1, s, f, w => do
    let (f, w) ← foldRoundA f w s
    foldRoundsA n (s / 2) f w

/-! ## The levels -/

/-- The query positions (`sampleQueriesAux`), received as the verifier samples them. -/
def sampleQueriesS (depth : ℕ) : ℕ → ℕ → Script (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← Script.sampleE)
      let n := min (128 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesS depth fuel (remaining - n)
      return chunk ++ rest

/-- The tail sumcheck on the final level's low part: per round the constant and quadratic
coefficients, then the challenge, both tables folded (`tail_sumcheck`,
`crates/pcs/src/whir.rs:704-719`). -/
def tailA (mu : ℕ) (w g : Array E) : Script Unit :=
  (sumcheckBy (fun st : Array E × Array E ↦ [roundC0A st.1 st.2, 0, roundC2A st.1 st.2])
    (fun st r ↦ (foldPairsA r st.1, foldPairsA r st.2)) (List.replicate mu none) (w, g)).bind
    fun _ ↦ .ret ()

/-- **The WHIR levels** (`recursive_prover_with_prepared_basis`, `crates/pcs/src/whir.rs:739-935`)
from a level whose lanes and weight are the tables `f` and `w`, `mu` the variables before its
folds: its fold rounds; then on the final level the folded lane, the queries and the tail; on
another the next level's commitment to the folded lane's low part, its high part, a grind, the
out-of-domain point and value, a grind, the queries and `λ`, the openings, and the claims glued
into the weight. -/
def levelsA : ℕ → List Whir.Level → Array E → Array E → Script Unit
  | _, [], _, _ => return ()
  | mu, level :: rest, f, w => do
    let (p, w) ← foldRoundsA level.fold (2 ^ level.fold) f w
    let mu := mu - level.fold
    let depth := mu + level.logInvRate
    match rest with
    | [] => do
      Script.sendList p.toList
      Script.grindBits Whir.queryGrindingBits
      let _ ← sampleQueriesS depth level.queries level.queries
      let _ ← Script.queryS
      tailA mu w (p.extract 0 (2 ^ mu))
    | next :: _ => do
      let low := p.extract 0 (2 ^ mu)
      Script.commitS (levelWordFast (mu - next.fold) next.fold next.logInvRate low)
      Script.sendList (p.extract (2 ^ mu) p.size).toList
      Script.grindBits Whir.oodGrindingBits
      let z ← Script.sampleN mu
      let e := eqTable z
      Script.sendE (dotA low e)
      Script.grindBits Whir.queryGrindingBits
      let queries ← sampleQueriesS depth level.queries level.queries
      let lam ← Script.sampleE
      let _ ← Script.queryS
      levelsA mu rest low (glueTablesA lam w [e, queryTableA mu queries (powers lam queries.length)])

/-- **The honest prover of the stacked opening** (`verify_stacked_opening`, then `verify_whir`):
receive the batching challenge, then run the levels from the stack table and the weight table of
the claims. -/
def openingFast (μ R : ℕ) (stack : Array K) (claims : List ClaimDesc) : Script Unit := do
  let c ← Script.sampleE
  let scales := powers c claims.length
  match Whir.ladder μ R with
  | none => return ()
  | some config => levelsA μ config (stackTableA μ stack) (basisTableA μ scales claims)

end LeanVM.Prover

end
