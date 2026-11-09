module

public import Common.Indiff.Defs

@[expose] public section

/-!
# Indifferentiability: the intermediate games

The proof that the real and ideal worlds of `Common.Indiff.Defs` are close goes through
intermediate games. All rooted values are drawn from a random oracle on *paths*: the value of the
rooted node with block path `β` is `val P β`, built from the random oracle `H` (for the digest
part, when `β` pads a message) and a second random oracle `T` on paths (`tSpec`). Because the
values are indexed by paths, it does not matter whether the sponge or the distinguisher reaches a
node first: both see the same value. The games:

* `funImpl`: the real world with `π` replaced by a lazily sampled random *function* in both
  directions (fresh answers uniform over all states, not only the unused ones).
* `combStep`: the *combined* game. Its state (`CState`) holds two views of the permutation: the
  *full* view `all`, every edge the real world would have (the distinguisher's queries and the
  sponge's), and the *visible* view `sim`, the simulator's state. Every step computes the real
  answer `aR` from the full view and the ideal answer `aI` from the visible view, drawing their
  randomness jointly, and raises the flag `diff` when they differ. Returning `aR` is the real
  world over random functions (`combReal`); returning `aI` is the ideal world (`combIdeal`). It
  also records the hashed messages and raises the flag `bad` when a simulator draw collides in
  its capacity with a capacity already visible.
* `visImpl`: the combined game's ideal side without the full view: the sponge's path queries are
  made and discarded (`skel`).
* `visEndImpl`: `visImpl` without those queries.
* `idealTImpl`: the simulator with its rooted values drawn from `val` (`visFwd`, `visInv`).
-/

open OracleComp OracleSpec

namespace Common

/-- The random oracle on block paths that supplies the simulator's rooted values. -/
abbrev tSpec (Dg E C : Type) : OracleSpec (List (Dg × E)) := List (Dg × E) →ₒ SpState Dg E C

/-- The random oracles of the intermediate games: `H` and the path oracle `T`. -/
abbrev aSpec (Msg Dg E C : Type) := roSpec Msg Dg + tSpec Dg E C

/-- The nonempty prefixes of a list, shortest first. -/
def prefixesOf {β : Type} (bs : List β) : List (List β) :=
  (List.range bs.length).map fun i ↦ bs.take (i + 1)

section Setting

variable {Dg E C Msg : Type}
  [XorOp Dg] [XorOp E] [XorCancel Dg] [XorCancel E]
  [DecidableEq Dg] [DecidableEq E] [DecidableEq C] [DecidableEq Msg]
  [Fintype Dg] [Fintype E] [Fintype C]
  [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- A uniform state, in the computations of the intermediate games. -/
noncomputable abbrev drawSt : OracleComp (unifSpec + aSpec Msg Dg E C) (SpState Dg E C) :=
  liftM ($ᵗ (SpState Dg E C))

/-- **The value of a path**: when `β` pads a message `m`, the digest `H m` with the rest of
`T β`; otherwise `T β`. -/
noncomputable def val (P : Padding Msg (Dg × E)) [P.Lawful] (β : List (Dg × E)) :
    OracleComp (unifSpec + aSpec Msg Dg E C) (SpState Dg E C) :=
  match P.unpad β with
  | some m => do
    let d ← hq (hs := aSpec Msg Dg E C) (.inl m)
    let t ← hq (hs := aSpec Msg Dg E C) (.inr β)
    pure ((d, t.1.2), t.2)
  | none => hq (hs := aSpec Msg Dg E C) (.inr β)

/-! ## Random functions -/

/-- The real world over a random function instead of a random permutation. -/
noncomputable def funImpl (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C)) (StateT (PermutationEdges (SpState Dg E C)) ProbComp)
  | .inl n => liftM (unifSpec.query n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => (spongeWith P iv (fun x ↦ lazyFun (.forward x)) m :
      StateT (PermutationEdges (SpState Dg E C)) ProbComp Dg)
  | .inr (.inr q) => lazyFun q

/-! ## The simulator over path values -/

/-- The simulator's forward step with rooted values from `val` and the uniform draw `u` for a
fresh unrooted node. Returns the answer, the new state, and the path and value of a fresh rooted
node, if any. -/
noncomputable def visFwd (P : Padding Msg (Dg × E)) [P.Lawful] (x u : SpState Dg E C)
    (σ : SimState Dg E C) :
    OracleComp (unifSpec + aSpec Msg Dg E C)
      (SpState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpState Dg E C)) :=
  match forwardLookup σ.edges x with
  | some y => pure (y, σ, none)
  | none =>
    match chainOf σ.chains x with
    | some (s, β) => do
      let v ← val P (β ++ [blockTo s x])
      pure (v, ⟨(x, v) :: σ.edges, (v, β ++ [blockTo s x]) :: σ.chains⟩,
        some (β ++ [blockTo s x], v))
    | none => pure (u, ⟨(x, u) :: σ.edges, σ.chains⟩, none)

/-- The simulator's inverse step with the uniform draw `u` for a fresh query. -/
def visInv (y u : SpState Dg E C) (σ : SimState Dg E C) : SpState Dg E C × SimState Dg E C :=
  match inverseLookup σ.edges y with
  | some x => (x, σ)
  | none => (u, ⟨(u, y) :: σ.edges, σ.chains⟩)

/-- The simulator with rooted values from `val`, drawing a uniform state at every query. -/
noncomputable def idealTImpl (P : Padding Msg (Dg × E)) [P.Lawful] :
    QueryImpl (dSpec Msg Dg (SpState Dg E C))
      (StateT (SimState Dg E C) (OracleComp (unifSpec + aSpec Msg Dg E C)))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + aSpec Msg Dg E C) _)
  | .inr (.inl m) => liftM (hq (hs := aSpec Msg Dg E C) (.inl m))
  | .inr (.inr (.forward x)) => StateT.mk fun σ ↦ do
      let u ← drawSt
      let r ← visFwd P x u σ
      pure (r.1, r.2.1)
  | .inr (.inr (.inverse y)) => StateT.mk fun σ ↦ do
      let u ← drawSt
      pure (visInv y u σ)

/-! ## The combined game -/

/-- The capacities visible to the distinguisher: the initial capacity and the capacities of both
ends of every simulator edge (the rooted states are among the edge ends). -/
def knownC (iv : SpState Dg E C) (σ : SimState Dg E C) : List C :=
  iv.2 :: σ.edges.flatMap fun e ↦ [e.1.2, e.2.2]

/-- The paths whose value has been queried: the simulator's rooted paths and the prefixes of the
padded hashed messages. -/
def usedPath (P : Padding Msg (Dg × E)) [P.Lawful] (VC : List (SpState Dg E C × List (Dg × E)))
    (hashed : List Msg) (β : List (Dg × E)) : Bool :=
  decide (β ∈ VC.map Prod.snd) || hashed.any fun m ↦ decide (β ∈ prefixesOf (P.pad m))

/-- The state of the combined game. -/
structure CState (Dg E C Msg : Type) where
  /-- The full view: every edge of the real world, newest first. -/
  all : PermutationEdges (SpState Dg E C)
  /-- The visible view: the simulator's state. -/
  sim : SimState Dg E C
  /-- The hashed messages, newest first. -/
  hashed : List Msg
  /-- Some answer of the full view differed from the visible view's. -/
  diff : Bool
  /-- Some simulator draw collided in its capacity with a visible capacity. -/
  bad : Bool

/-- The initial combined state. -/
def CState.init (iv : SpState Dg E C) : CState Dg E C Msg :=
  ⟨[], SimState.init iv, [], false, false⟩

/-- The full view's walk along the sponge path of a message: at each block, the value of the
path so far and a uniform state are drawn; a recorded node keeps its value, a fresh node takes
the path's value unless the path was already used, in which case it takes the uniform state. -/
noncomputable def allWalk (P : Padding Msg (Dg × E)) [P.Lawful] (used : List (Dg × E) → Bool) :
    List (Dg × E) → SpState Dg E C → PermutationEdges (SpState Dg E C) → List (Dg × E) →
      OracleComp (unifSpec + aSpec Msg Dg E C) (SpState Dg E C × PermutationEdges (SpState Dg E C))
  | _, s, A, [] => pure (s, A)
  | pre, s, A, B :: bs => do
    let v ← val P (pre ++ [B])
    let u ← drawSt
    match forwardLookup A (absorb s B) with
    | some y => allWalk P used (pre ++ [B]) y A bs
    | none =>
      let y := if used (pre ++ [B]) then u else v
      allWalk P used (pre ++ [B]) y ((absorb s B, y) :: A) bs

/-- The queries of `allWalk`, answers discarded. -/
noncomputable def skel (P : Padding Msg (Dg × E)) [P.Lawful] :
    List (Dg × E) → List (Dg × E) → OracleComp (unifSpec + aSpec Msg Dg E C) Unit
  | _, [] => pure ()
  | pre, B :: bs => do
    let _ ← val (C := C) P (pre ++ [B])
    let _ ← drawSt (Msg := Msg) (C := C)
    skel P (pre ++ [B]) bs

/-- The outcome of the combined forward step at `x`, given the shared uniform draw `u` and the
simulator's step `r`: the real answer from the full view (the recorded answer, or the value of
the fresh rooted path when unused, or `u`), the ideal answer `r.1`, and the new state. -/
def fwdOut (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) (cs : CState Dg E C Msg)
    (x u : SpState Dg E C)
    (r : SpState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpState Dg E C)) :
    (SpState Dg E C × SpState Dg E C) × CState Dg E C Msg :=
  let aR := match forwardLookup cs.all x with
    | some y => y
    | none => match r.2.2 with
      | some (β, v) => if usedPath P cs.sim.chains cs.hashed β then u else v
      | none => u
  let all' := match forwardLookup cs.all x with
    | some _ => cs.all
    | none => (x, aR) :: cs.all
  ((aR, r.1), ⟨all', r.2.1, cs.hashed, cs.diff || decide (aR ≠ r.1),
    cs.bad || ((forwardLookup cs.sim.edges x).isNone && decide (r.1.2 ∈ knownC iv cs.sim))⟩)

/-- The combined forward step: the real answer from the full view, the ideal answer from the
simulator, with one shared uniform draw. -/
noncomputable def combFwd (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C)
    (x : SpState Dg E C) :
    StateT (CState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C))
      (SpState Dg E C × SpState Dg E C) := StateT.mk fun cs ↦ do
  let u ← drawSt
  let r ← visFwd P x u cs.sim
  pure (fwdOut P iv cs x u r)

/-- The outcome of the combined inverse step at `y` with the uniform draw `u`. -/
def invOut (iv : SpState Dg E C) (cs : CState Dg E C Msg) (y u : SpState Dg E C) :
    (SpState Dg E C × SpState Dg E C) × CState Dg E C Msg :=
  let r := visInv y u cs.sim
  let aR := match inverseLookup cs.all y with
    | some x => x
    | none => u
  let all' := match inverseLookup cs.all y with
    | some _ => cs.all
    | none => (u, y) :: cs.all
  ((aR, r.1), ⟨all', r.2, cs.hashed, cs.diff || decide (aR ≠ r.1),
    cs.bad || ((inverseLookup cs.sim.edges y).isNone && decide (u.2 ∈ knownC iv cs.sim))⟩)

/-- The combined inverse step. -/
noncomputable def combInv (iv : SpState Dg E C) (y : SpState Dg E C) :
    StateT (CState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C))
      (SpState Dg E C × SpState Dg E C) := StateT.mk fun cs ↦ do
  let u ← drawSt
  pure (invOut iv cs y u)

/-- The outcome of the combined hash step at `m`, given the end `w` of the full view's walk and the
random oracle's digest `d`. -/
def hashOut (cs : CState Dg E C Msg) (m : Msg)
    (w : SpState Dg E C × PermutationEdges (SpState Dg E C)) (d : Dg) :
    (Dg × Dg) × CState Dg E C Msg :=
  ((w.1.1.1, d), ⟨w.2, cs.sim, m :: cs.hashed, cs.diff || decide (w.1.1.1 ≠ d), cs.bad⟩)

/-- The combined hash step: the real answer is the digest at the end of the full view's walk, the
ideal answer is the random oracle's. -/
noncomputable def combHash (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) (m : Msg) :
    StateT (CState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C)) (Dg × Dg) :=
  StateT.mk fun cs ↦ do
    let w ← allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m)
    let d ← hq (hs := aSpec Msg Dg E C) (.inl m)
    pure (hashOut cs m w d)

/-- The combined step, returning the real and the ideal answer. -/
noncomputable def combStep (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) :
    (t : (dSpec Msg Dg (SpState Dg E C)).Domain) →
      StateT (CState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C))
        ((dSpec Msg Dg (SpState Dg E C)).Range t × (dSpec Msg Dg (SpState Dg E C)).Range t)
  | .inl n => do
    let u ← liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + aSpec Msg Dg E C) _)
    pure (u, u)
  | .inr (.inl m) => combHash P iv m
  | .inr (.inr (.forward x)) => combFwd P iv x
  | .inr (.inr (.inverse y)) => combInv iv y

/-- The combined game answering with the full view: the real world over random functions. -/
noncomputable def combReal (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C))
      (StateT (CState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C))) :=
  fun t ↦ Prod.fst <$> combStep P iv t

/-- The combined game answering with the visible view: the ideal world. -/
noncomputable def combIdeal (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C))
      (StateT (CState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C))) :=
  fun t ↦ Prod.snd <$> combStep P iv t

/-! ## The visible games -/

/-- The visible state: the simulator's state, the hashed messages and the collision flag. -/
abbrev VState (Dg E C Msg : Type) := SimState Dg E C × List Msg × Bool

/-- The visible part of a combined state. -/
def CState.vis (cs : CState Dg E C Msg) : VState Dg E C Msg := (cs.sim, cs.hashed, cs.bad)

/-- The visible game: the combined game's ideal side without the full view. With `pre` the
sponge's path queries are made, answers discarded; without, they are not. -/
noncomputable def visImpl (P : Padding Msg (Dg × E)) [P.Lawful] (iv : SpState Dg E C) (pre : Bool) :
    QueryImpl (dSpec Msg Dg (SpState Dg E C))
      (StateT (VState Dg E C Msg) (OracleComp (unifSpec + aSpec Msg Dg E C)))
  | .inl n => liftM (liftM (unifSpec.query n : ProbComp (Fin (n + 1))) :
      OracleComp (unifSpec + aSpec Msg Dg E C) _)
  | .inr (.inl m) => StateT.mk fun vs ↦ do
      if pre then skel P [] (P.pad m) else pure ()
      let d ← hq (hs := aSpec Msg Dg E C) (.inl m)
      pure (d, (vs.1, m :: vs.2.1, vs.2.2))
  | .inr (.inr (.forward x)) => StateT.mk fun vs ↦ do
      let u ← drawSt
      let r ← visFwd P x u vs.1
      pure (r.1, (r.2.1, vs.2.1, vs.2.2 ||
        ((forwardLookup vs.1.edges x).isNone && decide (r.1.2 ∈ knownC iv vs.1))))
  | .inr (.inr (.inverse y)) => StateT.mk fun vs ↦ do
      let u ← drawSt
      let r := visInv y u vs.1
      pure (r.1, (r.2, vs.2.1, vs.2.2 ||
        ((inverseLookup vs.1.edges y).isNone && decide (u.2 ∈ knownC iv vs.1))))

end Setting

end Common
