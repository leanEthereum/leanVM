module

public import Statement.Prover.Ntt
public import Statement.Prover.Mle

/-!
# Ring switching and the WHIR opening

The honest prover of ring switching (`ringSwitch`: `ring_switch`,
`crates/verifier/src/ring_switch.rs:40-54`, with `ring_map` and `ring_weight`, `:12-34`) and of the
stacked opening (`verifyStackedOpening`: `verify_stacked_opening`,
`crates/verifier/src/lib.rs:124-139`, then `verify_whir`, `crates/verifier/src/whir.rs:142-265`), at
leanVM main `40f877dc2c858f013c5974ab71ca594b31a7aec9`, on arrays.

The claims are descriptions (`ClaimDesc`) whose denotations are the verifier's stack claims; their
weights are closures the prover does not evaluate on the cube: the starting weight table is built
by scatter, a column claim's equality kernel on its block of the stack and the ring claim's `Φ` of
the equality kernel on `q_keccak`'s block (`basisTableA`). The stack and weight tables are folded
in place round by round; a level's word is the additive NTT of its lanes (`levelWordFast`), and its
query table the queries' tensor products `∏_c (1, Ŵ_c(x_q))` summed (`queryTableA`).
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

/-! ## Ring switching -/

/-- What ring switching leaves for the opening: the target `Σ_i x^i Φ(s_i)`, the Keccak
reduction's point on `q_keccak`, and the six coefficients of the staged map `Φ`. -/
structure RingOut where
  target : E
  point : List E
  challenges : List E

/-- **The honest prover of ring switching**: it sends nothing; it receives the six coefficients
and returns the target with the point and the coefficients. -/
def ringFast (point slices : List E) : Script RingOut := do
  let challenges ← Script.sampleN ringMapShifts.length
  return ⟨polyEval (slices.map (phiMap · challenges)) gen, point, challenges⟩

/-! ## The claims -/

/-- A claim on the stack, as the opening receives it. -/
inductive ClaimDesc where
  /-- The ring-switching claim: its target, the Keccak reduction's point and the coefficients
  of `Φ`. -/
  | ring (layout : Layout) (target : E) (point challenges : List E)
  /-- A column claim. -/
  | column (layout : Layout) (claim : ColumnClaim)

/-- **The stack claim a description stands for**: the ring-switching claim with the weight
`ringWeight point · (ringCoefficients challenges)`, or the column claim on the stack. -/
def ClaimDesc.denote : ClaimDesc → StackClaim
  | .ring layout target point challenges =>
    ringSwitchClaim layout target fun rPrime ↦ ringWeight point rPrime (ringCoefficients challenges)
  | .column layout c =>
    (fun x ↦ eqEval ((layout.placement c.column).stackPoint c.point layout.stackLog) x, c.value)

/-- The ring-switching claim of ring switching's result. -/
def RingOut.claim (r : RingOut) (layout : Layout) : ClaimDesc :=
  .ring layout r.target r.point r.challenges

/-! ## Tables -/

/-- The constant coefficient `Σ_x W(0,x)·g(0,x)` of the round polynomial (`roundC0`). -/
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
claim's equality kernel on its block, the ring claim's `Φ ∘ eq` on the block of `q_keccak`. -/
def addClaim (μ : ℕ) (acc : Array E) (s : E) (d : ClaimDesc) : Array E :=
  match d with
  | .column layout c =>
    let pl := layout.placement c.column
    if c.point.length = pl.variableCount ∧ pl.variableCount ≤ μ ∧ layout.stackLog = μ then
      let vals := eqTable c.point
      addSlice (blockOff μ pl.variableCount pl.index) vals s vals.size acc
    else addFull μ d.denote.1 s acc
  | .ring layout _ point challenges =>
    let pl := layout.placement qkeccak
    if point.length = pl.variableCount ∧ pl.variableCount ≤ μ ∧ challenges.length = 6 then
      let vals := (eqTable point).map (phiMap · challenges)
      addSlice (blockOff μ pl.variableCount pl.index) vals s vals.size acc
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

/-! ## The rounds -/

/-- Send the round polynomial of `(W, g)` (its constant and quadratic coefficients) and return
the quadratic the verifier builds from them for the claim `claim` (`roundQuad`). -/
def roundA (claim : E) (W g : Array E) : Script (List E) := do
  let c0 := roundC0A W g
  let c2 := roundC2A W g
  Script.sendE c0
  Script.sendList [c2]
  return [c0, claim + sumE [c2], c2]

/-- A level's fold rounds: receive the challenge, fold both tables in place, send the next round
polynomial. -/
def foldRoundsA : ℕ → WhirState → List E → Array E → Array E →
    Script (WhirState × List E × Array E × Array E)
  | 0, s, levelFolds, W, g => return (s, levelFolds, W, g)
  | n + 1, s, levelFolds, W, g => do
    let challenge ← Script.sampleE
    let W' := foldPairsA challenge W
    let g' := foldPairsA challenge g
    let quad ← roundA (polyEval s.runningQuad challenge) W' g'
    foldRoundsA n { s with runningQuad := quad, folds := s.folds ++ [challenge] } (levelFolds ++
        [challenge]) W' g'

/-- The final level's tail rounds. -/
def tailRoundsA : ℕ → List E → Array E → Array E → Script Unit
  | 0, _, _, _ => return ()
  | n + 1, quad, W, g => do
    let challenge ← Script.sampleE
    if n = 0 then return ()
    else do
      let W' := foldPairsA challenge W
      let g' := foldPairsA challenge g
      let quad ← roundA (polyEval quad challenge) W' g'
      tailRoundsA n quad W' g'

/-- The query positions (`sampleQueriesAux`), received as the verifier samples them. -/
def sampleQueriesS (depth : ℕ) : ℕ → ℕ → Script (List ℕ)
  | 0, _ => return []
  | fuel + 1, remaining =>
    if remaining = 0 then return []
    else do
      let bits := eToNat (← Script.sampleE)
      let n := min (192 / depth) remaining
      let chunk := (List.range n).map fun c ↦ (bits >>> (c * depth)) % 2 ^ depth
      let rest ← sampleQueriesS depth fuel (remaining - n)
      return chunk ++ rest

/-- **The WHIR levels** from the level `index`, the verifier's state `s`, the weight table `W` and
the folded stack `g`. -/
def levelsA (μ : ℕ) : ℕ → List Whir.Level → WhirState → Array E → Array E → Script Unit
  | _, [], _, _, _ => return ()
  | index, level :: rest, s, W, g => do
    let (s, levelFolds, W, g) ← foldRoundsA level.fold s [] W g
    let messageLog := μ - s.folds.length
    let (residual, pending, tables) ← match rest with
      | [] => do
        Script.sendList g.toList
        pure (g, ([] : List (List E × (List E → E))), ([] : List (Array E)))
      | next :: _ => do
        Script.commitS (levelWordFast (messageLog - next.fold) next.fold next.logInvRate g)
        let oodPoint ← Script.sampleN messageLog
        let oodValue := mleA g oodPoint
        Script.sendE oodValue
        let T := eqTable oodPoint
        let quad ← roundA oodValue T g
        pure (#[], [(quad, fun x ↦ eqEval oodPoint x)], [T])
    Script.grindS
    let queries ← sampleQueriesS (messageLog + level.logInvRate) level.queries level.queries
    let lam ← Script.sampleE
    let queryWeights := powers lam queries.length
    let words ← Script.queryS
    let rows : List (List E) :=
      if index = 0 then words.map fun row ↦ row.reverse.map ofK else words.map extRow
    let enforced := enforcedSum rows levelFolds queryWeights
    let T := queryTableA messageLog queries queryWeights
    let quad ← roundA enforced T g
    let pending := pending ++ [(quad, fun x ↦ inducedWeight messageLog queries queryWeights x)]
    let s := glue lam s pending
    let W := glueTablesA lam W (tables ++ [T])
    match rest with
    | [] => tailRoundsA messageLog s.runningQuad W residual
    | _ :: _ => levelsA μ (index + 1) rest s W g

/-- **The honest prover of the stacked opening** (`verify_stacked_opening`, then `verify_whir`):
receive the batching challenge, then run the levels from the starting claim with the stack table
and the weight table of the claims. -/
def openingFast (μ R : ℕ) (stack : Array K) (claims : List ClaimDesc) : Script Unit := do
  let c ← Script.sampleE
  let scales := powers c claims.length
  match Whir.ladder μ R with
  | none => return ()
  | some config =>
    let f₀ := stackTableA μ stack
    let W₀ := basisTableA μ scales claims
    let target := dot scales (claims.map fun d ↦ d.denote.2)
    let quad ← roundA target W₀ f₀
    levelsA μ 0 config ⟨quad, [], []⟩ W₀ f₀

end LeanVM.Prover

end
