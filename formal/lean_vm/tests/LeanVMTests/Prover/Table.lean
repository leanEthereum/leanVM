import Statement.Prover.Table

/-!
# Tests: the executable table sumcheck on a toy instance

Six tables of log-heights `2, 1, 0, 3, 2, 1` (so three rounds), pseudo-random columns, a bus point
and degree-two forms. The round messages are consistent (each round's values at `0` and `1` sum to
the previous round's value at its challenge), the first round's sum is the summand summed over the
cube, the last round's value at its challenge is the terminal value the verifier computes from the
final evaluations, and the evaluations sent are the `159` columns'.
-/

namespace LeanVMTests.Prover.Table

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Prover

/-- The tables' log-heights. -/
def logs : List ℕ := [2, 1, 0, 3, 2, 1]

/-- The table holding global column `c`. -/
def tableOf (c : ℕ) : ℕ :=
  ((List.range 6).filter fun t ↦ globalColumnBases.getD t 0 ≤ c).getLast?.getD 0

/-- A pseudo-random element of `E`. -/
def el (n : ℕ) : E :=
  E.ofLimbs (K.ofBits (n * 2654435761 + 1)) (K.ofBits (n * 40503 + 5)) (K.ofBits (n + 77))

/-- Every global column, `2^τ_t` pseudo-random cells. -/
def cols : Array (Array K) := Array.ofFn (n := 165) fun c ↦
  Array.ofFn (n := 2 ^ logs.getD (tableOf c.val) 0) fun j ↦
    K.ofBits (c.val * 1000003 + j.val * 7919 + 17)

/-- A form of degree two in the first three columns. -/
def form (k : ℕ) : Form :=
  ⟨[([0], el (k + 1)), ([0, 1], el (k + 2)), ([], el (k + 3)), ([2, 2], el (k + 4))]⟩

/-- A bus result: its point and forms (its claims and totals unused). -/
def bus : BusResult :=
  ⟨[], [el 10, el 11, el 12, el 13], (List.range 6).map fun t ↦ [form t, form (t + 7), form (t + 13)],
    [0, 0, 0]⟩

def xi : E := el 99

def chal (k : ℕ) : E := el (200 + k)

def terms : Array (List (List ℕ × E)) := tableTermsOf xi bus

def F0 : Array (Array (Array E)) := tableInit cols

def sigma : Array E := tableSigmas bus.point logs terms F0

def st0 : TableState := ⟨F0, Array.replicate 6 1, logs.foldl max 0⟩

def round (st : TableState) : List E := tableRound bus.point logs terms sigma st

/-- The states after `0, 1, 2, 3` challenges. -/
def states : List TableState := (List.range 3).scanl (fun st k ↦ tableFold bus.point logs st (chal k)) st0

def st (k : ℕ) : TableState := states.getD k st0

/-- Row `y` of table `t` as the forms read it. -/
def rowOf (t y : ℕ) : ℕ → E := fun i ↦ ((F0.getD t #[]).getD i #[]).getD y 0

/-- The summand at the cube point `x`: every table's weight times its polynomial at its row. -/
def summandAt (x : ℕ) : E :=
  let b : List E := (List.range 3).map fun i ↦ if x.testBit i then 1 else 0
  ((List.range 6).map fun t ↦ (tableWeights logs bus.point b).getD t 0 *
    (Form.mk (terms.getD t [])).evaluate (rowOf t (x % 2 ^ logs.getD t 0))).sum

/-- The terminal value at the point, from the final evaluations. -/
def terminal : E :=
  let pt := ((List.range 3).map chal).reverse
  ((List.range 6).map fun t ↦ (tableWeights logs bus.point pt).getD t 0 *
    (Form.mk (terms.getD t [])).evaluate ((finalEvals ((st 3).cols.getD t #[])).getD · 0)).sum

#guard logs.foldl max 0 == 3
#guard polyEval (round (st 0)) 0 + polyEval (round (st 0)) 1 ==
  ((List.range 8).map summandAt).sum
#guard polyEval (round (st 1)) 0 + polyEval (round (st 1)) 1 == polyEval (round (st 0)) (chal 0)
#guard polyEval (round (st 2)) 0 + polyEval (round (st 2)) 1 == polyEval (round (st 1)) (chal 1)
#guard polyEval (round (st 2)) (chal 2) == terminal
#guard (tableEvals (st 3)).length == 159
#guard (st 3).free == 0

end LeanVMTests.Prover.Table
