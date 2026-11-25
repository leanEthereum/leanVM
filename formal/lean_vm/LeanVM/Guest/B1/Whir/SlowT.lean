/-
  LeanVM.Guest.B1.Whir.SlowT

  The templates of `residual_query_slow`, `level_residual_slow`, `level_residual_sum` and its loop.
-/

module

public import LeanVM.Guest.B1.Whir.Template
import LeanVM.Guest.StmtsAppend

/-!
# The slow residual's templates

`rqsBody pre yr vo` (`residual_query_slow__L{pre}_L{yr}_L{vo}`): coordinate `0`, its inverse `1`
folded away (`rqsHead`), then eleven values a coordinate `t` from `11 t` (`rqsStep`), the product
copied and returned. `lrsBody sum` (`level_residual_slow__L{Q}_L{pre}_L{yr}_L{vo}`): at a zero
flag the flag, else its `level_residual_sum` of the same shape, `sum`. `lsumBody Q loop`: its two
buffers, their first cells, its loop from `g^0` to `g^Q` and `acc[Q]`. `lrsLoopBody rq self`: an
iteration over `xq`, `rq` the level's `residual_query_slow`. `scripts/whir-data` checks every specialization against them
(`Whir/HelperAll.lean`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- Coordinate `0`: its challenge at `fold_cs`, its factor `1 + c + c·x` (the inverse `1`), and the
chain's first step. -/
def rqsHead (vo : ℕ) : List Stmt :=
  [.atom (.load (.n 3) (.n 1) 0), .atom (.const (.n 4) (word 1 0)), .atom (.add (.n 5) (.n 4) (.n 3)),
    .atom (.mul (.n 6) (.n 3) (.n 0)), .atom (.add (.n 7) (.n 5) (.n 6)),
    .atom (.const (.n 8) (word (vanishVal vo) 0)), .atom (.add (.n 9) (.n 0) (.n 8)),
    .atom (.mul (.n 10) (.n 0) (.n 9))]

/-- Coordinate `t ≥ 1`, its values from `11 t`: the challenge, the factor times the product so
far (value `11 t - 4`), the chain's step from `11 t - 1`. -/
def rqsStep (pre vo t : ℕ) : List Stmt :=
  [.atom (.load (.n (11 * t)) (.n (if t < pre then 1 else 2)) (if t < pre then t else t - pre)),
    .atom (.const (.n (11 * t + 1)) (word 1 0)),
    .atom (.add (.n (11 * t + 2)) (.n (11 * t + 1)) (.n (11 * t))),
    .atom (.const (.n (11 * t + 3)) (word (vanishInv (vo + t)) 0)),
    .atom (.mul (.n (11 * t + 4)) (.n (11 * t)) (.n (11 * t + 3))),
    .atom (.mul (.n (11 * t + 5)) (.n (11 * t + 4)) (.n (11 * t - 1))),
    .atom (.add (.n (11 * t + 6)) (.n (11 * t + 2)) (.n (11 * t + 5))),
    .atom (.mul (.n (11 * t + 7)) (.n (11 * t - 4)) (.n (11 * t + 6))),
    .atom (.const (.n (11 * t + 8)) (word (vanishVal (vo + t)) 0)),
    .atom (.add (.n (11 * t + 9)) (.n (11 * t - 1)) (.n (11 * t + 8))),
    .atom (.mul (.n (11 * t + 10)) (.n (11 * t - 1)) (.n (11 * t + 9)))]

/-- Coordinates `t .. t + f - 1`. -/
def rqsSteps (pre vo : ℕ) : ℕ → ℕ → List Stmt
  | _, 0 => []
  | t, f + 1 => rqsStep pre vo t ++ rqsSteps pre vo (t + 1) f

/-- The body before its `ret`: every coordinate, then the product copied. -/
def rqsPre (pre yr vo : ℕ) : List Stmt :=
  rqsHead vo ⧺ rqsSteps pre vo 1 (pre + yr - 1) ⧺
    [.atom (.copy (.n (11 * (pre + yr))) (.n (11 * (pre + yr) - 4)))]

/-- **`residual_query_slow__L{pre}_L{yr}_L{vo}`'s body.** -/
def rqsBody (pre yr vo : ℕ) : List Stmt := rqsPre pre yr vo ⧺ [.ret [.n (11 * (pre + yr))]]

/-- **The loop's body** (`xq, g^Q, acc, pw, positions, fold_cs, tail_cs, λ`), calling `rq`, the
level's `residual_query_slow`, and itself, `self`. -/
def lrsLoopBody (rq self : String) : List Stmt :=
  [.atom (.mul (.n 8) (.n 2) (.n 0)), .atom (.load (.n 9) (.n 8) 0),
    .atom (.mul (.n 10) (.n 3) (.n 0)), .atom (.load (.n 11) (.n 10) 0),
    .atom (.mul (.n 12) (.n 4) (.n 0)), .atom (.load (.n 13) (.n 12) 0),
    .call rq [.n 13, .n 5, .n 6] [.n 14],
    .atom (.mul (.n 15) (.n 11) (.n 14)), .atom (.add (.n 16) (.n 9) (.n 15)),
    .atom (.mul (.n 17) (.n 2) (.n 0)), .atom (.load (.n 16) (.n 17) 1),
    .atom (.mul (.n 18) (.n 3) (.n 0)), .atom (.load (.n 19) (.n 18) 0),
    .atom (.mul (.n 20) (.n 19) (.n 7)),
    .atom (.mul (.n 21) (.n 3) (.n 0)), .atom (.load (.n 20) (.n 21) 1),
    .atom (.const (.n 22) (word 2 0)), .atom (.mul (.n 23) (.n 0) (.n 22)),
    .atom (.add (.n 24) (.n 23) (.n 1)),
    .atom (.const (.n 25) (word 2 0)), .atom (.mul (.n 26) (.n 0) (.n 25)),
    .callIf (.n 24) self [.n 26, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7], .ret []]

/-- **`level_residual_sum`'s body** at `Q` queries, its loop `loop`. -/
def lsumBody (Q : ℕ) (loop : String) : List Stmt :=
  [.atom (.const (.n 4) (gw (Q + 1))), .atom (.hint (.allocDyn (.n 5) (.n 4))),
    .atom (.const (.n 6) (gw (Q + 1))), .atom (.hint (.allocDyn (.n 7) (.n 6))),
    .atom (.const (.n 8) (word 0 0)), .atom (.load (.n 8) (.n 5) 0),
    .atom (.mul (.n 9) (.n 3) (.n 3)), .atom (.load (.n 9) (.n 7) 0),
    .atom (.const (.n 10) (word 1 0)), .atom (.const (.n 11) (gw Q)),
    .atom (.add (.n 12) (.n 10) (.n 11)), .atom (.const (.n 13) (word 1 0)),
    .atom (.const (.n 14) (gw Q)),
    .callIf (.n 12) loop [.n 13, .n 14, .n 5, .n 7, .n 0, .n 1, .n 2, .n 3],
    .atom (.load (.n 15) (.n 5) Q), .ret [.n 15]]

/-- **`level_residual_slow`'s body**, its sum `sum`: at a zero flag the flag, else the sum. -/
def lrsBody (sum : String) : List Stmt :=
  [.ite (.n 4) [.atom (.copy (.n 5) (.n 4))] [.call sum [.n 0, .n 1, .n 2, .n 3] [.n 5]],
    .atom (.copy (.n 6) (.n 5)), .ret [.n 6]]

/-- The loop's parameters. -/
def lrsLoopParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]

/-- `level_residual_sum`'s parameters. -/
def lsumParams : List V := [.n 0, .n 1, .n 2, .n 3]

/-- `level_residual_slow`'s parameters. -/
def lrsParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4]

end
end LeanVM.Guest.B1.Whir
