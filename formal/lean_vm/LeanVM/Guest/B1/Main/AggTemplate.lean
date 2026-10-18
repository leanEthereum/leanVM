/-
  LeanVM.Guest.B1.Main.AggTemplate

  `aggregate_claims`' body (G:3319-3486) as a template: the opening absorb of the child count, the
  two inlined `eqtree`s, and the stores of the deferred claim, around its straight-line parts as the
  data writes them.
-/

module

public import LeanVM.Guest.B1.Main.AggregateSpec

/-!
# `aggregate_claims`' body

`agBody` is `Data.core29.body` (`core29_body`, by `decide +kernel` on `stmtsEqb`): the hints and
allocations (`agP1`), `obs(AGG_SEED, n_children)` (`fsCompressT`), the transcript, the two batching
sumchecks and their loops (`agP2`), the two `eqtree`s of the matrix point's halves (`eqtreeT`), the
weight loop and the final check (`agP3`), and the stores into `defer_stmt` (`agStores`).

`eqtreeT pt off out b` is `@inline eqtree(pt·g^off, out, 6)` (G:762-777) at its first value `b`:
`out[0..2) = [1 + r_0, r_0]`, then layer `t` doubling the previous one into
`out[2^(t+1) - 2 ..)`, each entry read back before it is multiplied.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Statements 0 to 9: the hints, the allocations, the batching transcript's seed. -/
def agP1 : List Stmt := [
    .atom (.hint (.alloc (.n 5) 44)),
    .atom (.hint (.witness "bc_sumcheck_msgs" (.heap (.n 5) 0 44))),
    .atom (.hint (.alloc (.n 6) 56)),
    .atom (.hint (.witness "mat_sumcheck_msgs" (.heap (.n 6) 0 56))),
    .atom (.hint (.witness "bc_star_hint" (.stack [.n 7]))),
    .atom (.hint (.witness "mat_stars_hint" (.stack [.n 8, .n 9]))),
    .atom (.hint (.allocDyn (.n 10) (.n 0))),
    .atom (.hint (.allocDyn (.n 11) (.n 0))),
    .atom (.const (.n 12) (word 13601591990776631179 14393745058652752134 0)),
    .atom (.const (.n 13) (word 10115303172019694088 4136606974476857268 0))]

/-- Statements 22 to 100: the transcript, the batching sumchecks and their loops. -/
def agP2 : List Stmt := [
    .atom (.const (.n 28) (word 2 0 0)),
    .atom (.mul (.n 29) (.n 0) (.n 28)),
    .atom (.mul (.n 30) (.n 29) (.n 29)),
    .atom (.hint (.allocDyn (.n 31) (.n 30))),
    .atom (.load (.n 26) (.n 31) 0),
    .atom (.load (.n 27) (.n 31) 1),
    .atom (.const (.n 32) (word 1 0 0)),
    .atom (.add (.n 33) (.n 32) (.n 0)),
    .atom (.const (.n 34) (word 1 0 0)),
    .callIf (.n 33) "__loop95" [.n 34, .n 0, .n 31, .n 1, .n 2, .n 10, .n 3, .n 11],
    .atom (.mul (.n 35) (.n 0) (.n 0)),
    .atom (.mul (.n 36) (.n 31) (.n 35)),
    .atom (.mul (.n 37) (.n 0) (.n 0)),
    .atom (.hint (.allocDyn (.n 38) (.n 37))),
    .atom (.const (.n 39) (word 2 0 0)),
    .atom (.mul (.n 40) (.n 0) (.n 39)),
    .atom (.mul (.n 41) (.n 40) (.n 40)),
    .atom (.mul (.n 42) (.n 41) (.n 40)),
    .atom (.hint (.allocDyn (.n 43) (.n 42))),
    .atom (.load (.n 44) (.n 36) 0),
    .atom (.load (.n 44) (.n 43) 0),
    .atom (.load (.n 45) (.n 36) 1),
    .atom (.load (.n 45) (.n 43) 1),
    .atom (.const (.n 46) (word 0 0 0)),
    .atom (.load (.n 46) (.n 43) 2),
    .atom (.const (.n 47) (word 1 0 0)),
    .atom (.add (.n 48) (.n 47) (.n 0)),
    .atom (.const (.n 49) (word 1 0 0)),
    .callIf (.n 48) "__loop96" [.n 49, .n 0, .n 43, .n 38, .n 10, .n 11],
    .atom (.mul (.n 50) (.n 0) (.n 0)),
    .atom (.mul (.n 51) (.n 50) (.n 0)),
    .atom (.mul (.n 52) (.n 43) (.n 51)),
    .atom (.load (.n 53) (.n 52) 0),
    .atom (.load (.n 54) (.n 52) 1),
    .atom (.load (.n 55) (.n 52) 2),
    .atom (.hint (.alloc (.n 56) 22)),
    .call "batch_sumcheck__L22" [.n 53, .n 54, .n 5, .n 55, .n 56] [.n 57, .n 58, .n 59],
    .atom (.copy (.n 60) (.n 57)),
    .atom (.copy (.n 61) (.n 58)),
    .atom (.const (.n 62) (word 2 0 0)),
    .atom (.mul (.n 63) (.n 0) (.n 62)),
    .atom (.hint (.allocDyn (.n 64) (.n 63))),
    .atom (.const (.n 65) (word 0 0 0)),
    .atom (.load (.n 65) (.n 64) 0),
    .atom (.const (.n 66) (word 1 0 0)),
    .atom (.add (.n 67) (.n 66) (.n 0)),
    .atom (.const (.n 68) (word 1 0 0)),
    .callIf (.n 67) "__loop97" [.n 68, .n 0, .n 10, .n 11, .n 56, .n 64, .n 38],
    .atom (.mul (.n 69) (.n 64) (.n 0)),
    .atom (.load (.n 70) (.n 69) 0),
    .atom (.mul (.n 71) (.n 7) (.n 70)),
    .atom (.assertEq (.n 59) (.n 71)),
    .atom (.mul (.n 72) (.n 0) (.n 0)),
    .atom (.mul (.n 73) (.n 72) (.n 0)),
    .atom (.hint (.allocDyn (.n 74) (.n 73))),
    .atom (.const (.n 75) (word 2 0 0)),
    .atom (.mul (.n 76) (.n 0) (.n 75)),
    .atom (.mul (.n 77) (.n 76) (.n 76)),
    .atom (.mul (.n 78) (.n 77) (.n 76)),
    .atom (.hint (.allocDyn (.n 79) (.n 78))),
    .atom (.load (.n 60) (.n 79) 0),
    .atom (.load (.n 61) (.n 79) 1),
    .atom (.const (.n 80) (word 0 0 0)),
    .atom (.load (.n 80) (.n 79) 2),
    .atom (.const (.n 81) (word 1 0 0)),
    .atom (.add (.n 82) (.n 81) (.n 0)),
    .atom (.const (.n 83) (word 1 0 0)),
    .callIf (.n 82) "__loop98" [.n 83, .n 0, .n 79, .n 74, .n 10, .n 11],
    .atom (.mul (.n 84) (.n 0) (.n 0)),
    .atom (.mul (.n 85) (.n 84) (.n 0)),
    .atom (.mul (.n 86) (.n 79) (.n 85)),
    .atom (.load (.n 87) (.n 86) 0),
    .atom (.load (.n 88) (.n 86) 1),
    .atom (.load (.n 89) (.n 86) 2),
    .atom (.hint (.alloc (.n 90) 28)),
    .call "batch_sumcheck__L28" [.n 87, .n 88, .n 6, .n 89, .n 90] [.n 91, .n 92, .n 93],
    .atom (.copy (.n 94) (.n 91)),
    .atom (.copy (.n 95) (.n 92)),
    .atom (.hint (.alloc (.n 96) 126))]

/-- The first value of `eqtree`'s layer `t ≥ 1`. -/
def etBase (b t : ℕ) : ℕ := b + 3 * t + 3 * 2 ^ t - 6

/-- Entry `i` of `eqtree`'s layer `t ≥ 1`: the previous layer's entry read, times `1 + r_t` and
`r_t`, stored. -/
def etEntry (out : V) (b t i : ℕ) : List Stmt :=
  [.atom (.load (.n (etBase b t + 3 + 3 * i)) out (2 ^ t - 2 + i)),
    .atom (.mul (.n (etBase b t + 4 + 3 * i)) (.n (etBase b t + 3 + 3 * i)) (.n (etBase b t + 2))),
    .atom (.load (.n (etBase b t + 4 + 3 * i)) out (2 ^ (t + 1) - 2 + i)),
    .atom (.mul (.n (etBase b t + 5 + 3 * i)) (.n (etBase b t + 3 + 3 * i)) (.n (etBase b t))),
    .atom (.load (.n (etBase b t + 5 + 3 * i)) out (2 ^ (t + 1) - 2 + 2 ^ t + i))]

/-- `eqtree`'s layer `t ≥ 1`: the coordinate `r_t`, `1 + r_t`, the entries. -/
def etLayer (pt : V) (off : ℕ) (out : V) (b t : ℕ) : List Stmt :=
  [.atom (.load (.n (etBase b t)) pt (off + t)), .atom (.const (.n (etBase b t + 1)) (word 1 0 0)),
    .atom (.add (.n (etBase b t + 2)) (.n (etBase b t + 1)) (.n (etBase b t)))] ++
    ((List.range (2 ^ t)).map (etEntry out b t)).flatten

/-- `eqtree(pt·g^off, out, 6)` at its first value `b`. -/
def eqtreeT (pt : V) (off : ℕ) (out : V) (b : ℕ) : List Stmt :=
  [.atom (.load (.n b) pt off), .atom (.const (.n (b + 1)) (word 1 0 0)),
    .atom (.add (.n (b + 2)) (.n (b + 1)) (.n b)), .atom (.load (.n (b + 2)) out 0),
    .atom (.load (.n b) out 1)] ++
    ((List.range 5).map fun t => etLayer pt off out b (t + 1)).flatten

/-- Statements 767 to 786: the weight loop and the final check. -/
def agP3 : List Stmt := [
    .atom (.const (.n 506) (word 2 0 0)),
    .atom (.mul (.n 507) (.n 0) (.n 506)),
    .atom (.mul (.n 508) (.n 507) (.n 507)),
    .atom (.hint (.allocDyn (.n 509) (.n 508))),
    .atom (.const (.n 510) (word 0 0 0)),
    .atom (.load (.n 510) (.n 509) 0),
    .atom (.const (.n 511) (word 0 0 0)),
    .atom (.load (.n 511) (.n 509) 1),
    .atom (.const (.n 512) (word 1 0 0)),
    .atom (.add (.n 513) (.n 512) (.n 0)),
    .atom (.const (.n 514) (word 1 0 0)),
    .callIf (.n 513) "__loop99" [.n 514, .n 0, .n 10, .n 96, .n 90, .n 301, .n 11, .n 74, .n 509],
    .atom (.mul (.n 515) (.n 0) (.n 0)),
    .atom (.mul (.n 516) (.n 509) (.n 515)),
    .atom (.load (.n 517) (.n 516) 0),
    .atom (.mul (.n 518) (.n 8) (.n 517)),
    .atom (.load (.n 519) (.n 516) 1),
    .atom (.mul (.n 520) (.n 9) (.n 519)),
    .atom (.add (.n 521) (.n 518) (.n 520)),
    .atom (.assertEq (.n 93) (.n 521))]

/-- The stores of the deferred claim: the bytecode point, its value, the matrix point, the two
values. -/
def agStores : List Stmt :=
  ((List.range 22).map fun k => [.atom (.load (.n (522 + k)) (.n 56) k),
      .atom (.load (.n (522 + k)) (.n 4) k)]).flatten ++
    [.atom (.load (.n 7) (.n 4) 22)] ++
    ((List.range 28).map fun k => [.atom (.load (.n (544 + k)) (.n 90) k),
      .atom (.load (.n (544 + k)) (.n 4) (23 + k))]).flatten ++
    [.atom (.load (.n 8) (.n 4) 51), .atom (.load (.n 9) (.n 4) 52)]

/-- `aggregate_claims`' body. -/
def agBody : List Stmt :=
  agP1 ++ fsCompressT (.n 12) (.n 13) (.n 0) 14 1 ++ agP2 ++ eqtreeT (.n 90) 0 (.n 96) 97 ++
    [.atom (.hint (.alloc (.n 301) 126))] ++ eqtreeT (.n 90) 14 (.n 301) 302 ++ agP3 ++ agStores ++
    [.ret []]

set_option maxRecDepth 100000 in
theorem core29_body : Fn.body Data.core29 = agBody := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Main
