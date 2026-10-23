/-
  LeanVM.Protocol.Compile.Spec

  A compositional calculus for doom certificates: specifications of sub-programs of the verifier
  language with a doom predicate and an escape potential, composed through `bind`, and the
  doom certificate of a whole program they yield.
-/

module

public import LeanVM.Protocol.Compile.Prog

/-!
# Specifications of verifier programs

A `Cert` (`LeanVM.Protocol.Compile.Prog`) is stated on whole histories of a whole program. The
leanVM verifier is a long `do`-block of sub-programs (sumcheck rounds, the bus, the WHIR levels),
and its groups of challenges straddle sub-programs (the ring-switching challenges and the
opening's batching challenge; the query positions and the level's `λ`). `Spec` is a
specification of a sub-program, run after any history `h₀`, that composes through `bind` and
gives a `Cert` for the whole program (`Spec.toCert`).

A specification `Spec p Pre Post εmax L T` carries

* `D h₀ l`, a doom predicate on the local history `l` of a run of `p` after `h₀`, meaningful at
  boundaries (after a prover move), before moves, and where `p` returns;
* `V h₀ l ≤ 1`, an *escape potential*: an upper bound on the probability, over the challenges
  still to come in the current group, that the group ends outside doom, *including* the lead of
  whatever runs after `p` when `p` returns within the group. It is a supermartingale over
  challenges (`sample`), does not grow at openings (`query`), is `1` wherever doom fails at the
  end of a group or at a return (`moveEnd`, `retEnd`), is at least the follower's lead `T`
  (capped at `1`) at a return in doom (`retDoom`), and at every boundary in doom, discounted by
  the proof of work just passed, is at most `εmax` (`bound`);
* the lead `L`, the potential at the start under `Pre`.

`Pre` makes doom hold at the start; `Post` holds where `p` returns in doom. The fields other than
the start conditions hold for every `h₀`: a specification sets `V := 1` where its assumptions
fail.

Composition (`Spec.bind`): from `Spec p Pre Post εmax Lp Lf` and `Spec (f a) (Post a) Q εmax Lf T`
for every `a`, `Spec (p.bind f) Pre Q εmax Lp T`: inside `p` the potential is `p`'s, at a return
of `p` in doom it is `f`'s start (at most `Lf`, hence at most `p`'s by `retDoom`), and after it
`f`'s. An earlier formulation charged the follower's lead through a return probability in
`bound`; it double-counted returns outside doom and its `bind` rule was false (a checked
counterexample is recorded in the branch's notes). The leaves: `ret`, `fail`, a read, a sample
(with its bad-challenge count), a proof of work (whose boundary discounts the follower's lead), a
commitment, an opening, and a joint bound for a sub-program with no prover move
(`Spec.ofNoMove`), which is how the query positions of a WHIR level get their product bound.
-/

namespace LeanVM.Protocol.Compile

open LeanVM.Parameters

@[expose] public section

variable {α β : Type}

/-! ## Local runs -/

namespace Prog

/-- The node is a prover move: a read, a proof of work or a commitment. -/
def IsMove : Prog α → Prop
  | read _ => True
  | grind _ _ => True
  | commit _ _ _ => True
  | _ => False

/-- The runs of `p` started after the history `h₀`: local histories, every opening answered from
the words committed in `h₀` and before it in the run. -/
inductive Reach (p : Prog α) (h₀ : List Ev) : List Ev → Prop where
  | nil : Reach p h₀ []
  | read {l k} (x : E) : Reach p h₀ l → p.after l = some (read k) →
      Reach p h₀ (l ++ [Ev.read x])
  | sample {l k} (c : E) : Reach p h₀ l → p.after l = some (sample k) →
      Reach p h₀ (l ++ [Ev.sample c])
  | grind {l b k} : Reach p h₀ l → p.after l = some (grind b k) →
      Reach p h₀ (l ++ [Ev.grind b])
  | commit {l ht w k} (word : Word) : Reach p h₀ l → p.after l = some (commit ht w k) →
      WellShaped w word → Reach p h₀ (l ++ [Ev.commit ht w word])
  | query {l i ps k rows} : Reach p h₀ l → p.after l = some (query i ps k) →
      answer (h₀ ++ l) i ps = some rows → Reach p h₀ (l ++ [Ev.query rows])

end Prog

/-- A local history ends with a prover move. -/
def EndsMove (l : List Ev) : Prop :=
  match l.getLast? with
  | some (Ev.read _) => True
  | some (Ev.grind _) => True
  | some (Ev.commit _ _ _) => True
  | _ => False

/-! ## Specifications -/

/-- A **specification** of the sub-program `p`: see the module docstring. -/
structure Spec (p : Prog α) (Pre : List Ev → Prop) (Post : α → List Ev → Prop)
    (εmax L T : ENNReal) where
  /-- Doom, on the local history after `h₀`. -/
  D : List Ev → List Ev → Prop
  /-- The escape potential. -/
  V : List Ev → List Ev → ENNReal
  /-- The potential is a probability bound. -/
  le_one : ∀ h₀ l, V h₀ l ≤ 1
  /-- Doom at the start. -/
  start_D : ∀ h₀, Pre h₀ → D h₀ []
  /-- The lead. -/
  start_V : ∀ h₀, Pre h₀ → V h₀ [] ≤ L
  /-- A scalar keeps doom. -/
  read : ∀ {h₀ l k} (x : E), p.Reach h₀ l → p.after l = some (.read k) → D h₀ l →
    D h₀ (l ++ [Ev.read x])
  /-- A proof of work keeps doom. -/
  grind : ∀ {h₀ l b k}, p.Reach h₀ l → p.after l = some (.grind b k) → D h₀ l →
    D h₀ (l ++ [Ev.grind b])
  /-- A well-shaped commitment keeps doom. -/
  commit : ∀ {h₀ l ht w k} (word : Word), p.Reach h₀ l → p.after l = some (.commit ht w k) →
    WellShaped w word → D h₀ l → D h₀ (l ++ [Ev.commit ht w word])
  /-- The potential is a supermartingale over a challenge. -/
  sample : ∀ {h₀ l k}, p.Reach h₀ l → p.after l = some (.sample k) →
    (Fintype.card E : ENNReal)⁻¹ * ∑ c : E, V h₀ (l ++ [Ev.sample c]) ≤ V h₀ l
  /-- An opening does not raise the potential. -/
  query : ∀ {h₀ l i ps k rows}, p.Reach h₀ l → p.after l = some (.query i ps k) →
    answer (h₀ ++ l) i ps = some rows → V h₀ (l ++ [Ev.query rows]) ≤ V h₀ l
  /-- Before a prover move outside doom, the potential is `1`. -/
  moveEnd : ∀ {h₀ l q}, p.Reach h₀ l → p.after l = some q → q.IsMove → ¬ D h₀ l → 1 ≤ V h₀ l
  /-- At a return outside doom, the potential is `1`. -/
  retEnd : ∀ {h₀ l a}, p.Reach h₀ l → p.after l = some (.ret a) → ¬ D h₀ l → 1 ≤ V h₀ l
  /-- At a return in doom, the potential covers the follower's lead. -/
  retDoom : ∀ {h₀ l a}, p.Reach h₀ l → p.after l = some (.ret a) → D h₀ l → min 1 T ≤ V h₀ l
  /-- Returning in doom gives the postcondition. -/
  post : ∀ {h₀ l a}, p.Reach h₀ l → p.after l = some (.ret a) → D h₀ l → Post a (h₀ ++ l)
  /-- At a boundary in doom, the discounted potential is at most `εmax`. -/
  bound : ∀ {h₀ l}, p.Reach h₀ l → l ≠ [] → EndsMove l → D h₀ l →
    (2 : ENNReal)⁻¹ ^ grindBits l * V h₀ l ≤ εmax

end
end LeanVM.Protocol.Compile
