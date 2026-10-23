/-
  LeanVM.Guest.B1.Tables.GkrComplete10

  `__loop10` backward: one pair of GKR levels from the honest words in memory.
-/

module

public import LeanVM.Guest.B1.Tables.GkrComplete

/-!
# `__loop10`, one iteration backward

`l10Vals` are the honest values of one iteration's body, from the layer's slots, the round
states the sumcheck leaves, the twelve children and the chain along them (`l10cv`).
`loop10_back`: with the memory holding the layer, the head and tail round states, the children,
the next row's two challenges and the next layer's slots, and `__loop101` and the next iteration
holding, the iteration holds.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The honest values of an `fs_next` block from its first, the word read. -/
def gkrFsv (x : E) (cv : Digest) : ℕ → E
  | 0 => x
  | k + 1 => fsVals x cv 1 k

/-- The chain after the first `i` children. -/
def l10cv (cvT : Digest) (es : ℕ → E) : ℕ → Digest
  | 0 => cvT
  | i + 1 => obsCv (l10cv cvT es i) (es i)

/-- The honest values `6 ..` of one iteration of `__loop10`. -/
noncomputable def l10Vals (x N dsb gmu layers rounds shE : E) (cv : Digest) (cur v0 v1 v2 row pos : E)
    (cvT : Digest) (curT claimT : E) (es : ℕ → E) : List E :=
  [x * x,
    dsb * gmu,
    shE,
    (x * x) * shE,
    ((x * x) * shE) * ((x * x) * shE),
    (((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE)),
    ((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE))) * ((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE))),
    layers * (((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE))) * ((((x * x) * shE) * ((x * x) * shE)) * (((x * x) * shE) * ((x * x) * shE)))),
    (digestScalars cv).1,
    (digestScalars cv).2,
    (sqVals cv 0),
    (sqVals cv 1),
    (sqVals cv 2),
    (sqVals cv 3),
    (sqVals cv 4),
    (sqVals cv 5),
    (sqVals cv 6),
    (sqVals cv 7),
    (sqVals cv 8),
    (sqVals cv 9),
    (sqVals cv 10),
    (sqVals cv 11),
    (sqVals cv 12),
    (sqVals cv 13),
    row,
    pos,
    pos * pos,
    (pos * pos) * (pos * pos),
    rounds * ((pos * pos) * (pos * pos)),
    cur,
    v0,
    v1,
    v2,
    ((sqVals cv 13)) * v2,
    v1 + (((sqVals cv 13)) * v2),
    ((sqVals cv 13)) * (v1 + (((sqVals cv 13)) * v2)),
    v0 + (((sqVals cv 13)) * (v1 + (((sqVals cv 13)) * v2))),
    word 1 0 0,
    (word 1 0 0) + ((x * x) * shE),
    word 1 0 0,
    word 1099511627776 0 0,
    row * (word 1099511627776 0 0),
    pos * ((x * x) * shE),
    (pos * ((x * x) * shE)) * (pos * ((x * x) * shE)),
    ((pos * ((x * x) * shE)) * (pos * ((x * x) * shE))) * ((pos * ((x * x) * shE)) * (pos * ((x * x) * shE))),
    rounds * (((pos * ((x * x) * shE)) * (pos * ((x * x) * shE))) * ((pos * ((x * x) * shE)) * (pos * ((x * x) * shE)))),
    (digestScalars cvT).1,
    (digestScalars cvT).2,
    curT,
    claimT,
    (es 0),
    (gkrFsv (es 0) (l10cv cvT es 0) 1),
    (gkrFsv (es 0) (l10cv cvT es 0) 2),
    (gkrFsv (es 0) (l10cv cvT es 0) 3),
    (gkrFsv (es 0) (l10cv cvT es 0) 4),
    (gkrFsv (es 0) (l10cv cvT es 0) 5),
    (gkrFsv (es 0) (l10cv cvT es 0) 6),
    (gkrFsv (es 0) (l10cv cvT es 0) 7),
    (gkrFsv (es 0) (l10cv cvT es 0) 8),
    (gkrFsv (es 0) (l10cv cvT es 0) 9),
    (gkrFsv (es 0) (l10cv cvT es 0) 10),
    (gkrFsv (es 0) (l10cv cvT es 0) 11),
    (gkrFsv (es 0) (l10cv cvT es 0) 12),
    (gkrFsv (es 0) (l10cv cvT es 0) 13),
    (gkrFsv (es 0) (l10cv cvT es 0) 14),
    (es 0),
    (es 1),
    (gkrFsv (es 1) (l10cv cvT es 1) 1),
    (gkrFsv (es 1) (l10cv cvT es 1) 2),
    (gkrFsv (es 1) (l10cv cvT es 1) 3),
    (gkrFsv (es 1) (l10cv cvT es 1) 4),
    (gkrFsv (es 1) (l10cv cvT es 1) 5),
    (gkrFsv (es 1) (l10cv cvT es 1) 6),
    (gkrFsv (es 1) (l10cv cvT es 1) 7),
    (gkrFsv (es 1) (l10cv cvT es 1) 8),
    (gkrFsv (es 1) (l10cv cvT es 1) 9),
    (gkrFsv (es 1) (l10cv cvT es 1) 10),
    (gkrFsv (es 1) (l10cv cvT es 1) 11),
    (gkrFsv (es 1) (l10cv cvT es 1) 12),
    (gkrFsv (es 1) (l10cv cvT es 1) 13),
    (gkrFsv (es 1) (l10cv cvT es 1) 14),
    (es 1),
    (es 2),
    (gkrFsv (es 2) (l10cv cvT es 2) 1),
    (gkrFsv (es 2) (l10cv cvT es 2) 2),
    (gkrFsv (es 2) (l10cv cvT es 2) 3),
    (gkrFsv (es 2) (l10cv cvT es 2) 4),
    (gkrFsv (es 2) (l10cv cvT es 2) 5),
    (gkrFsv (es 2) (l10cv cvT es 2) 6),
    (gkrFsv (es 2) (l10cv cvT es 2) 7),
    (gkrFsv (es 2) (l10cv cvT es 2) 8),
    (gkrFsv (es 2) (l10cv cvT es 2) 9),
    (gkrFsv (es 2) (l10cv cvT es 2) 10),
    (gkrFsv (es 2) (l10cv cvT es 2) 11),
    (gkrFsv (es 2) (l10cv cvT es 2) 12),
    (gkrFsv (es 2) (l10cv cvT es 2) 13),
    (gkrFsv (es 2) (l10cv cvT es 2) 14),
    (es 2),
    (es 3),
    (gkrFsv (es 3) (l10cv cvT es 3) 1),
    (gkrFsv (es 3) (l10cv cvT es 3) 2),
    (gkrFsv (es 3) (l10cv cvT es 3) 3),
    (gkrFsv (es 3) (l10cv cvT es 3) 4),
    (gkrFsv (es 3) (l10cv cvT es 3) 5),
    (gkrFsv (es 3) (l10cv cvT es 3) 6),
    (gkrFsv (es 3) (l10cv cvT es 3) 7),
    (gkrFsv (es 3) (l10cv cvT es 3) 8),
    (gkrFsv (es 3) (l10cv cvT es 3) 9),
    (gkrFsv (es 3) (l10cv cvT es 3) 10),
    (gkrFsv (es 3) (l10cv cvT es 3) 11),
    (gkrFsv (es 3) (l10cv cvT es 3) 12),
    (gkrFsv (es 3) (l10cv cvT es 3) 13),
    (gkrFsv (es 3) (l10cv cvT es 3) 14),
    (es 3),
    (es 4),
    (gkrFsv (es 4) (l10cv cvT es 4) 1),
    (gkrFsv (es 4) (l10cv cvT es 4) 2),
    (gkrFsv (es 4) (l10cv cvT es 4) 3),
    (gkrFsv (es 4) (l10cv cvT es 4) 4),
    (gkrFsv (es 4) (l10cv cvT es 4) 5),
    (gkrFsv (es 4) (l10cv cvT es 4) 6),
    (gkrFsv (es 4) (l10cv cvT es 4) 7),
    (gkrFsv (es 4) (l10cv cvT es 4) 8),
    (gkrFsv (es 4) (l10cv cvT es 4) 9),
    (gkrFsv (es 4) (l10cv cvT es 4) 10),
    (gkrFsv (es 4) (l10cv cvT es 4) 11),
    (gkrFsv (es 4) (l10cv cvT es 4) 12),
    (gkrFsv (es 4) (l10cv cvT es 4) 13),
    (gkrFsv (es 4) (l10cv cvT es 4) 14),
    (es 4),
    (es 5),
    (gkrFsv (es 5) (l10cv cvT es 5) 1),
    (gkrFsv (es 5) (l10cv cvT es 5) 2),
    (gkrFsv (es 5) (l10cv cvT es 5) 3),
    (gkrFsv (es 5) (l10cv cvT es 5) 4),
    (gkrFsv (es 5) (l10cv cvT es 5) 5),
    (gkrFsv (es 5) (l10cv cvT es 5) 6),
    (gkrFsv (es 5) (l10cv cvT es 5) 7),
    (gkrFsv (es 5) (l10cv cvT es 5) 8),
    (gkrFsv (es 5) (l10cv cvT es 5) 9),
    (gkrFsv (es 5) (l10cv cvT es 5) 10),
    (gkrFsv (es 5) (l10cv cvT es 5) 11),
    (gkrFsv (es 5) (l10cv cvT es 5) 12),
    (gkrFsv (es 5) (l10cv cvT es 5) 13),
    (gkrFsv (es 5) (l10cv cvT es 5) 14),
    (es 5),
    (es 6),
    (gkrFsv (es 6) (l10cv cvT es 6) 1),
    (gkrFsv (es 6) (l10cv cvT es 6) 2),
    (gkrFsv (es 6) (l10cv cvT es 6) 3),
    (gkrFsv (es 6) (l10cv cvT es 6) 4),
    (gkrFsv (es 6) (l10cv cvT es 6) 5),
    (gkrFsv (es 6) (l10cv cvT es 6) 6),
    (gkrFsv (es 6) (l10cv cvT es 6) 7),
    (gkrFsv (es 6) (l10cv cvT es 6) 8),
    (gkrFsv (es 6) (l10cv cvT es 6) 9),
    (gkrFsv (es 6) (l10cv cvT es 6) 10),
    (gkrFsv (es 6) (l10cv cvT es 6) 11),
    (gkrFsv (es 6) (l10cv cvT es 6) 12),
    (gkrFsv (es 6) (l10cv cvT es 6) 13),
    (gkrFsv (es 6) (l10cv cvT es 6) 14),
    (es 6),
    (es 7),
    (gkrFsv (es 7) (l10cv cvT es 7) 1),
    (gkrFsv (es 7) (l10cv cvT es 7) 2),
    (gkrFsv (es 7) (l10cv cvT es 7) 3),
    (gkrFsv (es 7) (l10cv cvT es 7) 4),
    (gkrFsv (es 7) (l10cv cvT es 7) 5),
    (gkrFsv (es 7) (l10cv cvT es 7) 6),
    (gkrFsv (es 7) (l10cv cvT es 7) 7),
    (gkrFsv (es 7) (l10cv cvT es 7) 8),
    (gkrFsv (es 7) (l10cv cvT es 7) 9),
    (gkrFsv (es 7) (l10cv cvT es 7) 10),
    (gkrFsv (es 7) (l10cv cvT es 7) 11),
    (gkrFsv (es 7) (l10cv cvT es 7) 12),
    (gkrFsv (es 7) (l10cv cvT es 7) 13),
    (gkrFsv (es 7) (l10cv cvT es 7) 14),
    (es 7),
    (es 8),
    (gkrFsv (es 8) (l10cv cvT es 8) 1),
    (gkrFsv (es 8) (l10cv cvT es 8) 2),
    (gkrFsv (es 8) (l10cv cvT es 8) 3),
    (gkrFsv (es 8) (l10cv cvT es 8) 4),
    (gkrFsv (es 8) (l10cv cvT es 8) 5),
    (gkrFsv (es 8) (l10cv cvT es 8) 6),
    (gkrFsv (es 8) (l10cv cvT es 8) 7),
    (gkrFsv (es 8) (l10cv cvT es 8) 8),
    (gkrFsv (es 8) (l10cv cvT es 8) 9),
    (gkrFsv (es 8) (l10cv cvT es 8) 10),
    (gkrFsv (es 8) (l10cv cvT es 8) 11),
    (gkrFsv (es 8) (l10cv cvT es 8) 12),
    (gkrFsv (es 8) (l10cv cvT es 8) 13),
    (gkrFsv (es 8) (l10cv cvT es 8) 14),
    (es 8),
    (es 9),
    (gkrFsv (es 9) (l10cv cvT es 9) 1),
    (gkrFsv (es 9) (l10cv cvT es 9) 2),
    (gkrFsv (es 9) (l10cv cvT es 9) 3),
    (gkrFsv (es 9) (l10cv cvT es 9) 4),
    (gkrFsv (es 9) (l10cv cvT es 9) 5),
    (gkrFsv (es 9) (l10cv cvT es 9) 6),
    (gkrFsv (es 9) (l10cv cvT es 9) 7),
    (gkrFsv (es 9) (l10cv cvT es 9) 8),
    (gkrFsv (es 9) (l10cv cvT es 9) 9),
    (gkrFsv (es 9) (l10cv cvT es 9) 10),
    (gkrFsv (es 9) (l10cv cvT es 9) 11),
    (gkrFsv (es 9) (l10cv cvT es 9) 12),
    (gkrFsv (es 9) (l10cv cvT es 9) 13),
    (gkrFsv (es 9) (l10cv cvT es 9) 14),
    (es 9),
    (es 10),
    (gkrFsv (es 10) (l10cv cvT es 10) 1),
    (gkrFsv (es 10) (l10cv cvT es 10) 2),
    (gkrFsv (es 10) (l10cv cvT es 10) 3),
    (gkrFsv (es 10) (l10cv cvT es 10) 4),
    (gkrFsv (es 10) (l10cv cvT es 10) 5),
    (gkrFsv (es 10) (l10cv cvT es 10) 6),
    (gkrFsv (es 10) (l10cv cvT es 10) 7),
    (gkrFsv (es 10) (l10cv cvT es 10) 8),
    (gkrFsv (es 10) (l10cv cvT es 10) 9),
    (gkrFsv (es 10) (l10cv cvT es 10) 10),
    (gkrFsv (es 10) (l10cv cvT es 10) 11),
    (gkrFsv (es 10) (l10cv cvT es 10) 12),
    (gkrFsv (es 10) (l10cv cvT es 10) 13),
    (gkrFsv (es 10) (l10cv cvT es 10) 14),
    (es 10),
    (es 11),
    (gkrFsv (es 11) (l10cv cvT es 11) 1),
    (gkrFsv (es 11) (l10cv cvT es 11) 2),
    (gkrFsv (es 11) (l10cv cvT es 11) 3),
    (gkrFsv (es 11) (l10cv cvT es 11) 4),
    (gkrFsv (es 11) (l10cv cvT es 11) 5),
    (gkrFsv (es 11) (l10cv cvT es 11) 6),
    (gkrFsv (es 11) (l10cv cvT es 11) 7),
    (gkrFsv (es 11) (l10cv cvT es 11) 8),
    (gkrFsv (es 11) (l10cv cvT es 11) 9),
    (gkrFsv (es 11) (l10cv cvT es 11) 10),
    (gkrFsv (es 11) (l10cv cvT es 11) 11),
    (gkrFsv (es 11) (l10cv cvT es 11) 12),
    (gkrFsv (es 11) (l10cv cvT es 11) 13),
    (gkrFsv (es 11) (l10cv cvT es 11) 14),
    (es 11),
    ((es 8)) * ((es 9)),
    (((es 8)) * ((es 9))) * ((es 10)),
    ((((es 8)) * ((es 9))) * ((es 10))) * ((es 11)),
    word 0 0 0,
    ((sqVals cv 13)) * (word 0 0 0),
    (((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqVals cv 13)) * (word 0 0 0)),
    ((es 4)) * ((es 5)),
    (((es 4)) * ((es 5))) * ((es 6)),
    ((((es 4)) * ((es 5))) * ((es 6))) * ((es 7)),
    ((sqVals cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqVals cv 13)) * (word 0 0 0))),
    (((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqVals cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqVals cv 13)) * (word 0 0 0)))),
    ((es 0)) * ((es 1)),
    (((es 0)) * ((es 1))) * ((es 2)),
    ((((es 0)) * ((es 1))) * ((es 2))) * ((es 3)),
    ((sqVals cv 13)) * ((((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqVals cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqVals cv 13)) * (word 0 0 0))))),
    (((((es 0)) * ((es 1))) * ((es 2))) * ((es 3))) + (((sqVals cv 13)) * ((((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqVals cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqVals cv 13)) * (word 0 0 0)))))),
    (sqVals (l10cv cvT es 12) 0),
    (sqVals (l10cv cvT es 12) 1),
    (sqVals (l10cv cvT es 12) 2),
    (sqVals (l10cv cvT es 12) 3),
    (sqVals (l10cv cvT es 12) 4),
    (sqVals (l10cv cvT es 12) 5),
    (sqVals (l10cv cvT es 12) 6),
    (sqVals (l10cv cvT es 12) 7),
    (sqVals (l10cv cvT es 12) 8),
    (sqVals (l10cv cvT es 12) 9),
    (sqVals (l10cv cvT es 12) 10),
    (sqVals (l10cv cvT es 12) 11),
    (sqVals (l10cv cvT es 12) 12),
    (sqVals (l10cv cvT es 12) 13),
    (sqVals (sqCv (l10cv cvT es 12)) 0),
    (sqVals (sqCv (l10cv cvT es 12)) 1),
    (sqVals (sqCv (l10cv cvT es 12)) 2),
    (sqVals (sqCv (l10cv cvT es 12)) 3),
    (sqVals (sqCv (l10cv cvT es 12)) 4),
    (sqVals (sqCv (l10cv cvT es 12)) 5),
    (sqVals (sqCv (l10cv cvT es 12)) 6),
    (sqVals (sqCv (l10cv cvT es 12)) 7),
    (sqVals (sqCv (l10cv cvT es 12)) 8),
    (sqVals (sqCv (l10cv cvT es 12)) 9),
    (sqVals (sqCv (l10cv cvT es 12)) 10),
    (sqVals (sqCv (l10cv cvT es 12)) 11),
    (sqVals (sqCv (l10cv cvT es 12)) 12),
    (sqVals (sqCv (l10cv cvT es 12)) 13),
    word 4096 0 0,
    curT * (word 4096 0 0),
    ((es 0)) + ((es 1)),
    ((sqVals (l10cv cvT es 12) 13)) * (((es 0)) + ((es 1))),
    ((es 0)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 0)) + ((es 1)))),
    ((es 2)) + ((es 3)),
    ((sqVals (l10cv cvT es 12) 13)) * (((es 2)) + ((es 3))),
    ((es 2)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 2)) + ((es 3)))),
    (((es 0)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((es 2)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 2)) + ((es 3))))),
    ((sqVals (sqCv (l10cv cvT es 12)) 13)) * ((((es 0)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((es 2)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 2)) + ((es 3)))))),
    (((es 0)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((sqVals (sqCv (l10cv cvT es 12)) 13)) * ((((es 0)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 0)) + ((es 1))))) + (((es 2)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 2)) + ((es 3))))))),
    ((es 4)) + ((es 5)),
    ((sqVals (l10cv cvT es 12) 13)) * (((es 4)) + ((es 5))),
    ((es 4)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 4)) + ((es 5)))),
    ((es 6)) + ((es 7)),
    ((sqVals (l10cv cvT es 12) 13)) * (((es 6)) + ((es 7))),
    ((es 6)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 6)) + ((es 7)))),
    (((es 4)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((es 6)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 6)) + ((es 7))))),
    ((sqVals (sqCv (l10cv cvT es 12)) 13)) * ((((es 4)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((es 6)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 6)) + ((es 7)))))),
    (((es 4)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((sqVals (sqCv (l10cv cvT es 12)) 13)) * ((((es 4)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 4)) + ((es 5))))) + (((es 6)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 6)) + ((es 7))))))),
    ((es 8)) + ((es 9)),
    ((sqVals (l10cv cvT es 12) 13)) * (((es 8)) + ((es 9))),
    ((es 8)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 8)) + ((es 9)))),
    ((es 10)) + ((es 11)),
    ((sqVals (l10cv cvT es 12) 13)) * (((es 10)) + ((es 11))),
    ((es 10)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 10)) + ((es 11)))),
    (((es 8)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((es 10)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 10)) + ((es 11))))),
    ((sqVals (sqCv (l10cv cvT es 12)) 13)) * ((((es 8)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((es 10)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 10)) + ((es 11)))))),
    (((es 8)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((sqVals (sqCv (l10cv cvT es 12)) 13)) * ((((es 8)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 8)) + ((es 9))))) + (((es 10)) + (((sqVals (l10cv cvT es 12) 13)) * (((es 10)) + ((es 11))))))),
    word 1099511627776 0 0,
    row * (word 1099511627776 0 0),
    pos * ((x * x) * shE),
    word 2 0 0,
    (pos * ((x * x) * shE)) * (word 2 0 0),
    word 2 0 0,
    x * (word 2 0 0),
    (x * (word 2 0 0)) + N,
    word 2 0 0,
    x * (word 2 0 0)]

def l10A0 : List Stmt :=
  [.atom (.mul (.n 6) (.n 0) (.n 0)),
    .atom (.mul (.n 7) (.n 2) (.n 3)),
    .atom (.load (.n 8) (.n 7) 0),
    .atom (.mul (.n 9) (.n 6) (.n 8)),
    .atom (.mul (.n 10) (.n 9) (.n 9)),
    .atom (.mul (.n 11) (.n 10) (.n 10)),
    .atom (.mul (.n 12) (.n 11) (.n 11)),
    .atom (.mul (.n 13) (.n 4) (.n 12)),
    .atom (.load (.n 14) (.n 13) 0),
    .atom (.load (.n 15) (.n 13) 1)]

def l10A1 : List Stmt :=
  [.atom (.load (.n 30) (.n 13) 6),
    .atom (.load (.n 31) (.n 13) 7),
    .atom (.mul (.n 32) (.n 31) (.n 31)),
    .atom (.mul (.n 33) (.n 32) (.n 32)),
    .atom (.mul (.n 34) (.n 5) (.n 33)),
    .atom (.load (.n 21) (.n 34) 0),
    .atom (.load (.n 22) (.n 34) 1),
    .atom (.load (.n 35) (.n 13) 2),
    .atom (.load (.n 35) (.n 34) 2),
    .atom (.load (.n 36) (.n 13) 3),
    .atom (.load (.n 37) (.n 13) 4),
    .atom (.load (.n 38) (.n 13) 5),
    .atom (.mul (.n 39) (.n 29) (.n 38)),
    .atom (.add (.n 40) (.n 37) (.n 39)),
    .atom (.mul (.n 41) (.n 29) (.n 40)),
    .atom (.add (.n 42) (.n 36) (.n 41)),
    .atom (.load (.n 42) (.n 34) 3),
    .atom (.const (.n 43) (word 1 0 0)),
    .atom (.add (.n 44) (.n 43) (.n 9)),
    .atom (.const (.n 45) (word 1 0 0)),
    .atom (.const (.n 46) (word 1099511627776 0 0)),
    .atom (.mul (.n 47) (.n 30) (.n 46)),
    .callIf (.n 44) "__loop101" [.n 45, .n 9, .n 5, .n 31, .n 30, .n 47],
    .atom (.mul (.n 48) (.n 31) (.n 9)),
    .atom (.mul (.n 49) (.n 48) (.n 48)),
    .atom (.mul (.n 50) (.n 49) (.n 49)),
    .atom (.mul (.n 51) (.n 5) (.n 50)),
    .atom (.load (.n 52) (.n 51) 0),
    .atom (.load (.n 53) (.n 51) 1),
    .atom (.load (.n 54) (.n 51) 2),
    .atom (.load (.n 55) (.n 51) 3)]

def l10A2 : List Stmt :=
  [.atom (.mul (.n 248) (.n 199) (.n 215)),
    .atom (.mul (.n 249) (.n 248) (.n 231)),
    .atom (.mul (.n 250) (.n 249) (.n 247)),
    .atom (.const (.n 251) (word 0 0 0)),
    .atom (.mul (.n 252) (.n 29) (.n 251)),
    .atom (.add (.n 253) (.n 250) (.n 252)),
    .atom (.mul (.n 254) (.n 135) (.n 151)),
    .atom (.mul (.n 255) (.n 254) (.n 167)),
    .atom (.mul (.n 256) (.n 255) (.n 183)),
    .atom (.mul (.n 257) (.n 29) (.n 253)),
    .atom (.add (.n 258) (.n 256) (.n 257)),
    .atom (.mul (.n 259) (.n 71) (.n 87)),
    .atom (.mul (.n 260) (.n 259) (.n 103)),
    .atom (.mul (.n 261) (.n 260) (.n 119)),
    .atom (.mul (.n 262) (.n 29) (.n 258)),
    .atom (.add (.n 263) (.n 261) (.n 262)),
    .atom (.assertEq (.n 55) (.n 263))]

def l10A3 : List Stmt :=
  [.atom (.load (.n 277) (.n 30) 40),
    .atom (.load (.n 291) (.n 30) 41),
    .atom (.load (.n 283) (.n 13) 16),
    .atom (.load (.n 284) (.n 13) 17),
    .atom (.const (.n 292) (word 4096 0 0)),
    .atom (.mul (.n 293) (.n 54) (.n 292)),
    .atom (.load (.n 293) (.n 13) 18),
    .atom (.add (.n 294) (.n 71) (.n 87)),
    .atom (.mul (.n 295) (.n 277) (.n 294)),
    .atom (.add (.n 296) (.n 71) (.n 295)),
    .atom (.add (.n 297) (.n 103) (.n 119)),
    .atom (.mul (.n 298) (.n 277) (.n 297)),
    .atom (.add (.n 299) (.n 103) (.n 298)),
    .atom (.add (.n 300) (.n 296) (.n 299)),
    .atom (.mul (.n 301) (.n 291) (.n 300)),
    .atom (.add (.n 302) (.n 296) (.n 301)),
    .atom (.load (.n 302) (.n 13) 19),
    .atom (.add (.n 303) (.n 135) (.n 151)),
    .atom (.mul (.n 304) (.n 277) (.n 303)),
    .atom (.add (.n 305) (.n 135) (.n 304)),
    .atom (.add (.n 306) (.n 167) (.n 183)),
    .atom (.mul (.n 307) (.n 277) (.n 306)),
    .atom (.add (.n 308) (.n 167) (.n 307)),
    .atom (.add (.n 309) (.n 305) (.n 308)),
    .atom (.mul (.n 310) (.n 291) (.n 309)),
    .atom (.add (.n 311) (.n 305) (.n 310)),
    .atom (.load (.n 311) (.n 13) 20),
    .atom (.add (.n 312) (.n 199) (.n 215)),
    .atom (.mul (.n 313) (.n 277) (.n 312)),
    .atom (.add (.n 314) (.n 199) (.n 313)),
    .atom (.add (.n 315) (.n 231) (.n 247)),
    .atom (.mul (.n 316) (.n 277) (.n 315)),
    .atom (.add (.n 317) (.n 231) (.n 316)),
    .atom (.add (.n 318) (.n 314) (.n 317)),
    .atom (.mul (.n 319) (.n 291) (.n 318)),
    .atom (.add (.n 320) (.n 314) (.n 319)),
    .atom (.load (.n 320) (.n 13) 21),
    .atom (.const (.n 321) (word 1099511627776 0 0)),
    .atom (.mul (.n 322) (.n 30) (.n 321)),
    .atom (.load (.n 322) (.n 13) 22),
    .atom (.mul (.n 323) (.n 31) (.n 9)),
    .atom (.const (.n 324) (word 2 0 0)),
    .atom (.mul (.n 325) (.n 323) (.n 324)),
    .atom (.load (.n 325) (.n 13) 23),
    .atom (.const (.n 326) (word 2 0 0)),
    .atom (.mul (.n 327) (.n 0) (.n 326)),
    .atom (.add (.n 328) (.n 327) (.n 1)),
    .atom (.const (.n 329) (word 2 0 0)),
    .atom (.mul (.n 330) (.n 0) (.n 329)),
    .callIf (.n 328) "__loop10" [.n 330, .n 1, .n 2, .n 3, .n 4, .n 5]]

def l10F : List Stmt :=
  (fsNextT (.n 52) (.n 53) (.n 54) 0 56 ++ [.atom (.copy (.n 71) (.n 56))]) ++
    (fsNextT (.n 69) (.n 70) (.n 54) 1 72 ++ [.atom (.copy (.n 87) (.n 72))]) ++
    (fsNextT (.n 85) (.n 86) (.n 54) 2 88 ++ [.atom (.copy (.n 103) (.n 88))]) ++
    (fsNextT (.n 101) (.n 102) (.n 54) 3 104 ++ [.atom (.copy (.n 119) (.n 104))]) ++
    (fsNextT (.n 117) (.n 118) (.n 54) 4 120 ++ [.atom (.copy (.n 135) (.n 120))]) ++
    (fsNextT (.n 133) (.n 134) (.n 54) 5 136 ++ [.atom (.copy (.n 151) (.n 136))]) ++
    (fsNextT (.n 149) (.n 150) (.n 54) 6 152 ++ [.atom (.copy (.n 167) (.n 152))]) ++
    (fsNextT (.n 165) (.n 166) (.n 54) 7 168 ++ [.atom (.copy (.n 183) (.n 168))]) ++
    (fsNextT (.n 181) (.n 182) (.n 54) 8 184 ++ [.atom (.copy (.n 199) (.n 184))]) ++
    (fsNextT (.n 197) (.n 198) (.n 54) 9 200 ++ [.atom (.copy (.n 215) (.n 200))]) ++
    (fsNextT (.n 213) (.n 214) (.n 54) 10 216 ++ [.atom (.copy (.n 231) (.n 216))]) ++
    (fsNextT (.n 229) (.n 230) (.n 54) 11 232 ++ [.atom (.copy (.n 247) (.n 232))])

theorem l10Pre_split : l10Pre = l10A0 ++ (squeezeT (.n 14) (.n 15) 16 ++ (l10A1 ++ (l10F ++
    (l10A2 ++ (squeezeT (.n 245) (.n 246) 264 ++ (squeezeT (.n 269) (.n 270) 278 ++ l10A3)))))) :=
  stmtsEqb_sound (by decide +kernel)

theorem word_g12' : word 4096 0 0 = gen ^ 12 := word_two_pow (a := 12) (by decide)

set_option maxHeartbeats 4000000 in
/-- **`__loop10`**, one iteration backward: from the memory's honest words and the callees. -/
theorem loop10_back {rd : Reader} (d : ℕ) {x N dsb gmu layers rounds shE : E} {cv cvT : Digest}
    {cur v0 v1 v2 row pos curT claimT : E} {es : ℕ → E}
    (hds : LoadHolds rd (dsb * gmu) 0 shE)
    (hl0 : LoadHolds rd (layers * (x * x * shE) ^ 8) 0 (digestScalars cv).1)
    (hl1 : LoadHolds rd (layers * (x * x * shE) ^ 8) 1 (digestScalars cv).2)
    (hl2 : LoadHolds rd (layers * (x * x * shE) ^ 8) 2 cur)
    (hl3 : LoadHolds rd (layers * (x * x * shE) ^ 8) 3 v0)
    (hl4 : LoadHolds rd (layers * (x * x * shE) ^ 8) 4 v1)
    (hl5 : LoadHolds rd (layers * (x * x * shE) ^ 8) 5 v2)
    (hl6 : LoadHolds rd (layers * (x * x * shE) ^ 8) 6 row)
    (hl7 : LoadHolds rd (layers * (x * x * shE) ^ 8) 7 pos)
    (hh0 : LoadHolds rd (rounds * pos ^ 4) 0 (digestScalars (sqCv cv)).1)
    (hh1 : LoadHolds rd (rounds * pos ^ 4) 1 (digestScalars (sqCv cv)).2)
    (hh2 : LoadHolds rd (rounds * pos ^ 4) 2 cur)
    (hh3 : LoadHolds rd (rounds * pos ^ 4) 3 (v0 + challengeOf (sqCv cv) * (v1 + challengeOf (sqCv cv) * v2)))
    (ht0 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 0 (digestScalars cvT).1)
    (ht1 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 1 (digestScalars cvT).2)
    (ht2 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 2 curT)
    (ht3 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 3 claimT)
    (hr0 : LoadHolds rd (row) 40 (challengeOf (sqCv (l10cv cvT es 12))))
    (hr1 : LoadHolds rd (row) 41 (challengeOf (sqCv (sqCv (l10cv cvT es 12)))))
    (hn16 : LoadHolds rd (layers * (x * x * shE) ^ 8) 16 (digestScalars (sqCv (sqCv (l10cv cvT es 12)))).1)
    (hn17 : LoadHolds rd (layers * (x * x * shE) ^ 8) 17 (digestScalars (sqCv (sqCv (l10cv cvT es 12)))).2)
    (hn18 : LoadHolds rd (layers * (x * x * shE) ^ 8) 18 (curT * gen ^ 12))
    (hn19 : LoadHolds rd (layers * (x * x * shE) ^ 8) 19 ((((es 0)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 0)) + ((es 1))))) + (((challengeOf (sqCv (sqCv (l10cv cvT es 12))))) * ((((es 0)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 0)) + ((es 1))))) + (((es 2)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 2)) + ((es 3)))))))))
    (hn20 : LoadHolds rd (layers * (x * x * shE) ^ 8) 20 ((((es 4)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 4)) + ((es 5))))) + (((challengeOf (sqCv (sqCv (l10cv cvT es 12))))) * ((((es 4)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 4)) + ((es 5))))) + (((es 6)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 6)) + ((es 7)))))))))
    (hn21 : LoadHolds rd (layers * (x * x * shE) ^ 8) 21 ((((es 8)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 8)) + ((es 9))))) + (((challengeOf (sqCv (sqCv (l10cv cvT es 12))))) * ((((es 8)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 8)) + ((es 9))))) + (((es 10)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 10)) + ((es 11)))))))))
    (hn22 : LoadHolds rd (layers * (x * x * shE) ^ 8) 22 (row * gen ^ 40))
    (hn23 : LoadHolds rd (layers * (x * x * shE) ^ 8) 23 (pos * (x * x * shE) * gen))
    (hK1 : IsInK (1 + (x * x * shE)))
    (h101 : 1 + (x * x * shE) ≠ 0 →
      coreProgram.relN rd d "__loop101" [1, (x * x * shE), rounds, pos, row, row * gen ^ 40] [])
    (hc : ∀ i < 12, LoadHolds rd curT i (es i))
    (hcheck : claimT = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCv cv) * (es 4 * es 5 * es 6 * es 7 + challengeOf (sqCv cv) * (es 8 * es 9 * es 10 * es 11)))
    (hK : IsInK (x * gen + N))
    (hnext : x * gen + N ≠ 0 → coreProgram.relN rd d "__loop10" [x * gen, N, dsb, gmu, layers, rounds] []) :
    coreProgram.relN rd (d + 1) "__loop10" [x, N, dsb, gmu, layers, rounds] [] := by
  rw [relN_succ_iff find_loop10]
  set σ := setl (Val.ofArgs [x, N, dsb, gmu, layers, rounds]) 6 (l10Vals x N dsb gmu layers rounds shE cv cur v0 v1 v2 row pos
    cvT curT claimT es) with hσ
  refine ⟨σ, rfl, ?_⟩
  have e13 : σ (.n 13) = layers * (x * x * shE) ^ 8 := by show layers * _ = _; ring
  have e34 : σ (.n 34) = rounds * pos ^ 4 := by show rounds * _ = _; ring
  have e51 : σ (.n 51) = rounds * (pos * (x * x * shE)) ^ 4 := by show rounds * _ = _; ring
  have e44 : σ (.n 44) = 1 + (x * x * shE) := by show word 1 0 0 + _ = _; rw [word_one]
  have e45 : σ (.n 45) = 1 := word_one
  have e47 : σ (.n 47) = row * gen ^ 40 := by show row * word 1099511627776 0 0 = _; rw [word_g40]
  have e328 : σ (.n 328) = x * gen + N := by show x * word 2 0 0 + N = _; rw [word_gen]
  have e330 : σ (.n 330) = x * gen := by show x * word 2 0 0 = _; rw [word_gen]
  rw [core40_body, holdsList_append, l10Pre_split]
  simp only [holdsList_append, l10F]
  simp only [l10A0, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨rfl, rfl, hds, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hl0), (by rw [e13]; exact hl1), ?_⟩
  rw [holds_squeezeT]
  refine ⟨⟨cv, rfl, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [l10A1, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨(by rw [e13]; exact hl6), (by rw [e13]; exact hl7), rfl, rfl, rfl, (by rw [e34]; exact hh0), (by rw [e34]; exact hh1), (by rw [e13]; exact hl2), (by rw [e34]; exact hh2), (by rw [e13]; exact hl3), (by rw [e13]; exact hl4), (by rw [e13]; exact hl5), rfl, rfl, rfl, rfl, (by rw [e34]; exact hh3), rfl, rfl, rfl, rfl, rfl, (by rw [e44]; exact hK1), (fun h => by rw [e44] at h; simp only [List.map_cons, List.map_nil]; rw [e45, e47]; exact h101 h), rfl, rfl, rfl, rfl, (by rw [e51]; exact ht0), (by rw [e51]; exact ht1), (by rw [e51]; exact ht2), (by rw [e51]; exact ht3), ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 0 (by norm_num), l10cv cvT es 0, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 1 (by norm_num), l10cv cvT es 1, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 2 (by norm_num), l10cv cvT es 2, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 3 (by norm_num), l10cv cvT es 3, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 4 (by norm_num), l10cv cvT es 4, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 5 (by norm_num), l10cv cvT es 5, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 6 (by norm_num), l10cv cvT es 6, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 7 (by norm_num), l10cv cvT es 7, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 8 (by norm_num), l10cv cvT es 8, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 9 (by norm_num), l10cv cvT es 9, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 10 (by norm_num), l10cv cvT es 10, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hc 11 (by norm_num), l10cv cvT es 11, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  simp only [l10A2, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [show σ (.n 263) = claimT from by show (((((es 0)) * ((es 1))) * ((es 2))) * ((es 3))) + (((sqVals cv 13)) * ((((((es 4)) * ((es 5))) * ((es 6))) * ((es 7))) + (((sqVals cv 13)) * ((((((es 8)) * ((es 9))) * ((es 10))) * ((es 11))) + (((sqVals cv 13)) * (word 0 0 0)))))) = claimT; rw [hcheck]; simp only [sqVals, word_zero]; ring]; exact e_add_self _), ?_⟩
  rw [holds_squeezeT]
  refine ⟨⟨l10cv cvT es 12, rfl, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  rw [holds_squeezeT]
  refine ⟨⟨sqCv (l10cv cvT es 12), rfl, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [l10A3, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨hr0, hr1, (by rw [e13]; exact hn16), (by rw [e13]; exact hn17), rfl, rfl, (by rw [e13]; rw [show σ (.n 293) = curT * gen ^ 12 from by show curT * word 4096 0 0 = _; rw [word_g12]]; exact hn18), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hn19), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hn20), rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [e13]; exact hn21), rfl, rfl, (by rw [e13]; rw [show σ (.n 322) = row * gen ^ 40 from by show row * word 1099511627776 0 0 = _; rw [word_g40]]; exact hn22), rfl, rfl, rfl, (by rw [e13]; rw [show σ (.n 325) = pos * (x * x * shE) * gen from by show pos * ((x * x) * shE) * word 2 0 0 = _; rw [word_gen]]; exact hn23), rfl, rfl, rfl, rfl, rfl, (by rw [e328]; exact hK), (fun h => by rw [e328] at h; simp only [List.map_cons, List.map_nil]; rw [e330]; exact hnext h), ?_⟩
  rfl

/-- Finitely many relations, each under its condition, hold at one depth. -/
theorem rel_uniform_cond {rd : Reader} {F : ℕ → String} {A R : ℕ → List E} {P : ℕ → Prop} :
    ∀ m : ℕ, (∀ j < m, P j → coreProgram.Rel rd (F j) (A j) (R j)) →
      ∃ D, ∀ j < m, P j → coreProgram.relN rd D (F j) (A j) (R j)
  | 0, _ => ⟨0, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | m + 1, h => by
    classical
    obtain ⟨D, hD⟩ := rel_uniform_cond m fun j hj => h j (by omega)
    by_cases hp : P m
    · obtain ⟨D', hD'⟩ := h m (by omega) hp
      refine ⟨max D D', fun j hj hpj => ?_⟩
      rcases Nat.lt_or_ge j m with hj' | hj'
      · exact relN_mono coreProgram (le_max_left _ _) _ _ _ (hD j hj' hpj)
      · rw [show j = m by omega]; exact relN_mono coreProgram (le_max_right _ _) _ _ _ hD'
    · refine ⟨D, fun j hj hpj => ?_⟩
      rcases Nat.lt_or_ge j m with hj' | hj'
      · exact hD j hj' hpj
      · exact absurd (show P m by rw [show m = j by omega]; exact hpj) hp

/-- The memory and callee facts one iteration of `__loop10` needs, at `x`. -/
structure L10Iter (rd : Reader) (N dsb gmu layers rounds x shE : E) (cv cvT : Digest)
    (cur v0 v1 v2 row pos curT claimT : E) (es : ℕ → E) : Prop where
  hds : LoadHolds rd (dsb * gmu) 0 shE
  hl0 : LoadHolds rd (layers * (x * x * shE) ^ 8) 0 (digestScalars cv).1
  hl1 : LoadHolds rd (layers * (x * x * shE) ^ 8) 1 (digestScalars cv).2
  hl2 : LoadHolds rd (layers * (x * x * shE) ^ 8) 2 cur
  hl3 : LoadHolds rd (layers * (x * x * shE) ^ 8) 3 v0
  hl4 : LoadHolds rd (layers * (x * x * shE) ^ 8) 4 v1
  hl5 : LoadHolds rd (layers * (x * x * shE) ^ 8) 5 v2
  hl6 : LoadHolds rd (layers * (x * x * shE) ^ 8) 6 row
  hl7 : LoadHolds rd (layers * (x * x * shE) ^ 8) 7 pos
  hh0 : LoadHolds rd (rounds * pos ^ 4) 0 (digestScalars (sqCv cv)).1
  hh1 : LoadHolds rd (rounds * pos ^ 4) 1 (digestScalars (sqCv cv)).2
  hh2 : LoadHolds rd (rounds * pos ^ 4) 2 cur
  hh3 : LoadHolds rd (rounds * pos ^ 4) 3 (v0 + challengeOf (sqCv cv) * (v1 + challengeOf (sqCv cv) * v2))
  ht0 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 0 (digestScalars cvT).1
  ht1 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 1 (digestScalars cvT).2
  ht2 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 2 curT
  ht3 : LoadHolds rd (rounds * (pos * (x * x * shE)) ^ 4) 3 claimT
  hr0 : LoadHolds rd (row) 40 (challengeOf (sqCv (l10cv cvT es 12)))
  hr1 : LoadHolds rd (row) 41 (challengeOf (sqCv (sqCv (l10cv cvT es 12))))
  hn16 : LoadHolds rd (layers * (x * x * shE) ^ 8) 16 (digestScalars (sqCv (sqCv (l10cv cvT es 12)))).1
  hn17 : LoadHolds rd (layers * (x * x * shE) ^ 8) 17 (digestScalars (sqCv (sqCv (l10cv cvT es 12)))).2
  hn18 : LoadHolds rd (layers * (x * x * shE) ^ 8) 18 (curT * gen ^ 12)
  hn19 : LoadHolds rd (layers * (x * x * shE) ^ 8) 19 ((((es 0)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 0)) + ((es 1))))) + (((challengeOf (sqCv (sqCv (l10cv cvT es 12))))) * ((((es 0)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 0)) + ((es 1))))) + (((es 2)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 2)) + ((es 3))))))))
  hn20 : LoadHolds rd (layers * (x * x * shE) ^ 8) 20 ((((es 4)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 4)) + ((es 5))))) + (((challengeOf (sqCv (sqCv (l10cv cvT es 12))))) * ((((es 4)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 4)) + ((es 5))))) + (((es 6)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 6)) + ((es 7))))))))
  hn21 : LoadHolds rd (layers * (x * x * shE) ^ 8) 21 ((((es 8)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 8)) + ((es 9))))) + (((challengeOf (sqCv (sqCv (l10cv cvT es 12))))) * ((((es 8)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 8)) + ((es 9))))) + (((es 10)) + (((challengeOf (sqCv (l10cv cvT es 12)))) * (((es 10)) + ((es 11))))))))
  hn22 : LoadHolds rd (layers * (x * x * shE) ^ 8) 22 (row * gen ^ 40)
  hn23 : LoadHolds rd (layers * (x * x * shE) ^ 8) 23 (pos * (x * x * shE) * gen)
  hK1 : IsInK (1 + (x * x * shE))
  h101 : 1 + (x * x * shE) ≠ 0 → coreProgram.Rel rd "__loop101" [1, (x * x * shE), rounds, pos, row, row * gen ^ 40] []
  hc : ∀ i < 12, LoadHolds rd curT i (es i)
  hcheck : claimT = es 0 * es 1 * es 2 * es 3 + challengeOf (sqCv cv) * (es 4 * es 5 * es 6 * es 7 +
    challengeOf (sqCv cv) * (es 8 * es 9 * es 10 * es 11))

/-- **`__loop10`** runs the `m` pair iterations from their honest facts. -/
theorem loop10_complete {rd : Reader} {dsb gmu layers rounds : E} {m : ℕ} (hm0 : 0 < m)
    (hB : ∀ j < m, ∃ (shE : E) (cv cvT : Digest) (cur v0 v1 v2 row pos curT claimT : E) (es : ℕ → E),
      L10Iter rd (gen ^ m) dsb gmu layers rounds (gen ^ j) shE cv cvT cur v0 v1 v2 row pos curT claimT es) :
    coreProgram.Rel rd "__loop10" [1, gen ^ m, dsb, gmu, layers, rounds] [] := by
  choose shE cv cvT cur v0 v1 v2 row pos curT claimT es hI using hB
  classical
  obtain ⟨D, hD⟩ := rel_uniform_cond (rd := rd) (F := fun _ => "__loop101")
    (P := fun j => ∃ hj : j < m, 1 + gen ^ j * gen ^ j * shE j hj ≠ 0)
    (A := fun j => if hj : j < m then [1, gen ^ j * gen ^ j * shE j hj, rounds, pos j hj, row j hj,
      row j hj * gen ^ 40] else []) (R := fun _ => []) m fun j hj ⟨_, hne⟩ => by
        simp only [hj, ↓reduceDIte]; exact (hI j hj).h101 hne
  refine Main.loop_complete_from (D := D) (B := fun j => j < m) hm0 rfl (fun j hj => hj) ?_
  intro d j hd hj hK hnext
  have it := hI j hj
  refine loop10_back d it.hds it.hl0 it.hl1 it.hl2 it.hl3 it.hl4 it.hl5 it.hl6 it.hl7 it.hh0 it.hh1
    it.hh2 it.hh3 it.ht0 it.ht1 it.ht2 it.ht3 it.hr0 it.hr1 it.hn16 it.hn17 it.hn18 it.hn19 it.hn20
    it.hn21 it.hn22 it.hn23 it.hK1 (fun hne => ?_) it.hc it.hcheck hK hnext
  have := relN_mono coreProgram hd _ _ _ (hD j hj ⟨hj, hne⟩)
  simpa only [hj, ↓reduceDIte] using this

end
end LeanVM.Guest.B1.VerifySub
