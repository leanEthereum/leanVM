module

public import Statement.Prover.Script
public import Statement.Prover.Mle

/-!
# The batched GKR over three product trees, executable

The prover of `verifyGkrGrandProducts` (`crates/verifier/src/bus.rs:14-51`) over three trees of
`2^D` leaves, the first two of the same product, every layer built once (`treeLayers`). In a step of
`h` levels the three child layers are folded in place, one coordinate per round (`foldStride`), and
each round's polynomial is computed row by row from the folded layers (`gkrRound`); after the rounds
the folded layers are the children sent. The walk is the verifier's: one level first when the depth
is odd, two at a time after.
-/

@[expose] public section

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Protocol.Verifier

/-! ## Coefficient lists -/

/-- The coefficients (constant first) of `(a₀ + a₁·X)·P`, `prev` the coefficient of `P` before
the first one given. -/
def mulLineFrom (a₀ a₁ : E) : E → List E → List E
  | prev, [] => [a₁ * prev]
  | prev, p :: ps => (a₀ * p + a₁ * prev) :: mulLineFrom a₀ a₁ p ps

/-- The coefficients of `(a₀ + a₁·X)·P`. -/
def mulLine (a₀ a₁ : E) (P : List E) : List E := mulLineFrom a₀ a₁ 0 P

/-- `acc + w·v`, coefficient by coefficient. -/
def addScaled (acc v : List E) (w : E) : List E := List.zipWith (fun a b ↦ a + w * b) acc v

/-! ## The trees -/

/-- One level up a product tree: adjacent pairs multiplied. -/
def mulPairsA (t : Array E) : Array E :=
  Array.ofFn (n := t.size / 2) fun i ↦ t[2 * i.1]'(by omega) * t[2 * i.1 + 1]'(by omega)

/-- The layers of a product tree, from the leaves `t` to `n` levels up. -/
def treeLayers : ℕ → Array E → List (Array E)
  | 0, t => [t]
  | n + 1, t => t :: treeLayers n (mulPairsA t)

/-! ## One step -/

/-- The prover's state in a step's sumcheck: the three child layers, folded at the coordinates
bound so far, and the point's coordinates not yet bound. -/
structure GkrFold where
  t₀ : Array E
  t₁ : Array E
  t₂ : Array E
  rest : List E

/-- Bind the coordinate just above the `h` child bits at `r`: entry `j + 2^h·b` becomes
`(1 + r)·t[j + 2^h·2b] + r·t[j + 2^h·(2b + 1)]`. -/
def foldStride (h : ℕ) (r : E) (t : Array E) : Array E :=
  Array.ofFn (n := t.size / 2) fun i ↦
    let lo := i.1 % 2 ^ h + 2 ^ (h + 1) * (i.1 / 2 ^ h)
    (1 + r) * t.getD lo 0 + r * t.getD (lo + 2 ^ h) 0

/-- Row `b`'s product of the `2^h` lines `X ↦ (1 + X)·t[j + 2^h·2b] + X·t[j + 2^h·(2b + 1)]`, as
coefficients. -/
def lineProd (h : ℕ) (t : Array E) (b : ℕ) : List E :=
  Nat.fold (2 ^ h) (fun j _ P ↦
    let lo := t.getD (j + 2 ^ (h + 1) * b) 0
    let hi := t.getD (j + 2 ^ (h + 1) * b + 2 ^ h) 0
    mulLine lo (lo + hi) P) [1]

/-- **A round's polynomial**, `2^h + 1` coefficients: per row below the coordinate bound next, the
equality weight of the remaining coordinates times the three trees' line products batched by the
combiner `c`. -/
def gkrRound (h : ℕ) (c : E) (st : GkrFold) : List E :=
  let eqT := eqTable st.rest.tail
  let c2 := c * c
  Nat.fold eqT.size (fun b _ acc ↦
    addScaled acc (addScaled (addScaled (lineProd h st.t₀ b) (lineProd h st.t₁ b) c)
      (lineProd h st.t₂ b) c2) (eqT.getD b 0)) (List.replicate (2 ^ h + 1) 0)

/-- Bind the next coordinate at the challenge. -/
def gkrFold (h : ℕ) (st : GkrFold) (r : E) : GkrFold :=
  ⟨foldStride h r st.t₀, foldStride h r st.t₁, foldStride h r st.t₂, st.rest.tail⟩

/-- **One step of `h` levels** from the state `s`, the child layers `t₀, t₁, t₂`: the combiner,
the sumcheck on the folded layers, the children (the folded layers), the fresh coordinates; the
next state. -/
def gkrStepA (t₀ t₁ t₂ : Array E) (h : ℕ) (s : GkrState) : Script GkrState :=
  Script.sampleE.bind fun c ↦
  (sumcheckBy (gkrRound h c) (gkrFold h) (s.point.map some) ⟨t₀, t₁, t₂, s.point⟩).bind fun r ↦
    (Script.sendList r.2.t₀.toList).bind fun _ ↦
    (Script.sendList r.2.t₁.toList).bind fun _ ↦
    (Script.sendList r.2.t₂.toList).bind fun _ ↦
    (Script.sampleN h).bind fun y ↦
    .ret ⟨[multilinearEval r.2.t₀.toList y, multilinearEval r.2.t₁.toList y,
      multilinearEval r.2.t₂.toList y], y ++ r.1⟩

/-! ## The walk -/

/-- The walk from the layers `n` levels above the leaves, `Aᵢ` the trees' layers: one level first
when `n` is odd, two at a time after. -/
def gkrLayersA (A₀ A₁ A₂ : List (Array E)) : ℕ → GkrState → Script GkrState
  | 0, s => .ret s
  | 1, s =>
    (gkrStepA (A₀.getD 0 #[]) (A₁.getD 0 #[]) (A₂.getD 0 #[]) 1 s).bind (gkrLayersA A₀ A₁ A₂ 0)
  | n + 2, s =>
    if n % 2 = 1 then
      (gkrStepA (A₀.getD (n + 1) #[]) (A₁.getD (n + 1) #[]) (A₂.getD (n + 1) #[]) 1 s).bind
        (gkrLayersA A₀ A₁ A₂ (n + 1))
    else
      (gkrStepA (A₀.getD n #[]) (A₁.getD n #[]) (A₂.getD n #[]) 2 s).bind
        (gkrLayersA A₀ A₁ A₂ n)

/-- **The batched GKR** over trees of depth `D` whose layers are `A₀, A₁, A₂`: the shared root (the
first tree's), the third tree's root, the walk; the third root, the point and the leaves' values
there. -/
def gkrA (D : ℕ) (A₀ A₁ A₂ : List (Array E)) : Script (E × List E × List E) :=
  let r₀ := (A₀.getD D #[]).getD 0 0
  let r₂ := (A₂.getD D #[]).getD 0 0
  (Script.sendE r₀).bind fun _ ↦ (Script.sendE r₂).bind fun _ ↦
    (gkrLayersA A₀ A₁ A₂ D ⟨[r₀, r₀, r₂], []⟩).bind fun s ↦ .ret (r₂, s.point, s.values)

end LeanVM.Prover

end
