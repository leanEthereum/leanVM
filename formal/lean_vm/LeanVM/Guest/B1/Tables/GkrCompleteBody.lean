/-
  LeanVM.Guest.B1.Tables.GkrCompleteBody

  `verify_bus_gkr`'s body backward: its honest values (generated) and every statement holding.
-/

module

public import LeanVM.Guest.B1.Tables.GkrComplete10

/-!
# `verify_bus_gkr`'s body, backward

`vbgVals` are the honest values `5 ..` of `verify_bus_gkr`'s body: the stream's roots, the
first layer, the exponent tables, the odd layer (from its six children `oes`), and the last
layer's slots. `vbg_holds`: on a memory holding the words the body loads, every statement
holds, for any relation the two loops hold of.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- `cv0`: the state after the two roots. -/
abbrev vbgCv0 (cv : Digest) (x0 cnt : E) : Digest := obsCv (obsCv cv x0) cnt

/-- The honest values `5 ..` of `verify_bus_gkr`'s body. -/
noncomputable def vbgVals (fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 : E)
    (cv cvF : Digest) (oes : ℕ → E) : List E :=
  let cv0 := vbgCv0 cv x0 cnt
  [word 4 0 0,
    gmu * (word 4 0 0),
    (gmu * (word 4 0 0)) * (gmu * (word 4 0 0)),
    ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))) * ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))),
    (((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))) * ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0)))) * (((gmu * (word 4 0 0)) * (gmu * (word 4 0 0))) * ((gmu * (word 4 0 0)) * (gmu * (word 4 0 0)))),
    layers,
    rounds,
    pts,
    word 4294967296 0 0,
    rcy,
    rct1,
    rct2,
    fs0,
    fs1,
    x0,
    (gkrFsv x0 cv 1),
    (gkrFsv x0 cv 2),
    (gkrFsv x0 cv 3),
    (gkrFsv x0 cv 4),
    (gkrFsv x0 cv 5),
    (gkrFsv x0 cv 6),
    (gkrFsv x0 cv 7),
    (gkrFsv x0 cv 8),
    (gkrFsv x0 cv 9),
    (gkrFsv x0 cv 10),
    (gkrFsv x0 cv 11),
    (gkrFsv x0 cv 12),
    (gkrFsv x0 cv 13),
    (gkrFsv x0 cv 14),
    cnt,
    (gkrFsv cnt (obsCv cv x0) 1),
    (gkrFsv cnt (obsCv cv x0) 2),
    (gkrFsv cnt (obsCv cv x0) 3),
    (gkrFsv cnt (obsCv cv x0) 4),
    (gkrFsv cnt (obsCv cv x0) 5),
    (gkrFsv cnt (obsCv cv x0) 6),
    (gkrFsv cnt (obsCv cv x0) 7),
    (gkrFsv cnt (obsCv cv x0) 8),
    (gkrFsv cnt (obsCv cv x0) 9),
    (gkrFsv cnt (obsCv cv x0) 10),
    (gkrFsv cnt (obsCv cv x0) 11),
    (gkrFsv cnt (obsCv cv x0) 12),
    (gkrFsv cnt (obsCv cv x0) 13),
    (gkrFsv cnt (obsCv cv x0) 14),
    word 0 0 0,
    cnt + (word 0 0 0),
    cinv,
    1,
    word 4 0 0,
    cur * (word 4 0 0),
    word 1 0 0,
    pb,
    dsb,
    word 1 0 0,
    word 1 0 0,
    word 1 0 0,
    word 2 0 0,
    word 2 0 0,
    word 1 0 0,
    word 2 0 0,
    word 2 0 0,
    word 4 0 0,
    word 1 0 0,
    word 4 0 0,
    word 2 0 0,
    word 8 0 0,
    word 1 0 0,
    word 8 0 0,
    word 2 0 0,
    word 16 0 0,
    word 1 0 0,
    word 16 0 0,
    word 2 0 0,
    word 32 0 0,
    word 1 0 0,
    word 32 0 0,
    word 2 0 0,
    word 64 0 0,
    word 1 0 0,
    word 64 0 0,
    word 2 0 0,
    word 128 0 0,
    word 1 0 0,
    word 128 0 0,
    word 2 0 0,
    word 256 0 0,
    word 1 0 0,
    word 256 0 0,
    word 2 0 0,
    word 512 0 0,
    word 1 0 0,
    word 512 0 0,
    word 2 0 0,
    word 1024 0 0,
    word 1 0 0,
    word 1024 0 0,
    word 2 0 0,
    word 2048 0 0,
    word 1 0 0,
    word 2048 0 0,
    word 2 0 0,
    word 4096 0 0,
    word 1 0 0,
    word 4096 0 0,
    word 2 0 0,
    word 8192 0 0,
    word 1 0 0,
    word 8192 0 0,
    word 2 0 0,
    word 16384 0 0,
    word 1 0 0,
    word 16384 0 0,
    word 2 0 0,
    word 32768 0 0,
    word 1 0 0,
    word 32768 0 0,
    word 2 0 0,
    word 65536 0 0,
    word 1 0 0,
    dsb * gmu,
    shE,
    word 1 0 0,
    shE + (word 1 0 0),
    (digestScalars cv0).1,
    (digestScalars cv0).2,
    (sqVals cv0 0),
    (sqVals cv0 1),
    (sqVals cv0 2),
    (sqVals cv0 3),
    (sqVals cv0 4),
    (sqVals cv0 5),
    (sqVals cv0 6),
    (sqVals cv0 7),
    (sqVals cv0 8),
    (sqVals cv0 9),
    (sqVals cv0 10),
    (sqVals cv0 11),
    (sqVals cv0 12),
    (sqVals cv0 13),
    (cur * word 4 0 0),
    x0,
    x0,
    cnt,
    ((sqVals cv0 13)) * cnt,
    x0 + (((sqVals cv0 13)) * cnt),
    ((sqVals cv0 13)) * (x0 + (((sqVals cv0 13)) * cnt)),
    x0 + (((sqVals cv0 13)) * (x0 + (((sqVals cv0 13)) * cnt))),
    pts,
    word 1099511627776 0 0,
    pts * (word 1099511627776 0 0),
    (oes 0),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 1),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 2),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 3),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 4),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 5),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 6),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 7),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 8),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 9),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 10),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 11),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 12),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 13),
    (gkrFsv (oes 0) (l10cv (sqCv cv0) oes 0) 14),
    (oes 0),
    (oes 1),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 1),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 2),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 3),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 4),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 5),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 6),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 7),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 8),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 9),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 10),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 11),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 12),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 13),
    (gkrFsv (oes 1) (l10cv (sqCv cv0) oes 1) 14),
    (oes 1),
    (oes 2),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 1),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 2),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 3),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 4),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 5),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 6),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 7),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 8),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 9),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 10),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 11),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 12),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 13),
    (gkrFsv (oes 2) (l10cv (sqCv cv0) oes 2) 14),
    (oes 2),
    (oes 3),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 1),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 2),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 3),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 4),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 5),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 6),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 7),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 8),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 9),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 10),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 11),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 12),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 13),
    (gkrFsv (oes 3) (l10cv (sqCv cv0) oes 3) 14),
    (oes 3),
    (oes 4),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 1),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 2),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 3),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 4),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 5),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 6),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 7),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 8),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 9),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 10),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 11),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 12),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 13),
    (gkrFsv (oes 4) (l10cv (sqCv cv0) oes 4) 14),
    (oes 4),
    (oes 5),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 1),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 2),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 3),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 4),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 5),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 6),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 7),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 8),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 9),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 10),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 11),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 12),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 13),
    (gkrFsv (oes 5) (l10cv (sqCv cv0) oes 5) 14),
    (oes 5),
    ((oes 4)) * ((oes 5)),
    word 0 0 0,
    ((sqVals cv0 13)) * (word 0 0 0),
    (((oes 4)) * ((oes 5))) + (((sqVals cv0 13)) * (word 0 0 0)),
    ((oes 2)) * ((oes 3)),
    ((sqVals cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqVals cv0 13)) * (word 0 0 0))),
    (((oes 2)) * ((oes 3))) + (((sqVals cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqVals cv0 13)) * (word 0 0 0)))),
    ((oes 0)) * ((oes 1)),
    ((sqVals cv0 13)) * ((((oes 2)) * ((oes 3))) + (((sqVals cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqVals cv0 13)) * (word 0 0 0))))),
    (((oes 0)) * ((oes 1))) + (((sqVals cv0 13)) * ((((oes 2)) * ((oes 3))) + (((sqVals cv0 13)) * ((((oes 4)) * ((oes 5))) + (((sqVals cv0 13)) * (word 0 0 0)))))),
    (sqVals (l10cv (sqCv cv0) oes 6) 0),
    (sqVals (l10cv (sqCv cv0) oes 6) 1),
    (sqVals (l10cv (sqCv cv0) oes 6) 2),
    (sqVals (l10cv (sqCv cv0) oes 6) 3),
    (sqVals (l10cv (sqCv cv0) oes 6) 4),
    (sqVals (l10cv (sqCv cv0) oes 6) 5),
    (sqVals (l10cv (sqCv cv0) oes 6) 6),
    (sqVals (l10cv (sqCv cv0) oes 6) 7),
    (sqVals (l10cv (sqCv cv0) oes 6) 8),
    (sqVals (l10cv (sqCv cv0) oes 6) 9),
    (sqVals (l10cv (sqCv cv0) oes 6) 10),
    (sqVals (l10cv (sqCv cv0) oes 6) 11),
    (sqVals (l10cv (sqCv cv0) oes 6) 12),
    (sqVals (l10cv (sqCv cv0) oes 6) 13),
    word 64 0 0,
    ((cur * word 4 0 0)) * (word 64 0 0),
    ((oes 0)) + ((oes 1)),
    ((sqVals (l10cv (sqCv cv0) oes 6) 13)) * (((oes 0)) + ((oes 1))),
    ((oes 0)) + (((sqVals (l10cv (sqCv cv0) oes 6) 13)) * (((oes 0)) + ((oes 1)))),
    ((oes 2)) + ((oes 3)),
    ((sqVals (l10cv (sqCv cv0) oes 6) 13)) * (((oes 2)) + ((oes 3))),
    ((oes 2)) + (((sqVals (l10cv (sqCv cv0) oes 6) 13)) * (((oes 2)) + ((oes 3)))),
    ((oes 4)) + ((oes 5)),
    ((sqVals (l10cv (sqCv cv0) oes 6) 13)) * (((oes 4)) + ((oes 5))),
    ((oes 4)) + (((sqVals (l10cv (sqCv cv0) oes 6) 13)) * (((oes 4)) + ((oes 5)))),
    word 2 0 0,
    word 1 0 0,
    pb * gmu,
    npair,
    (word 1 0 0) + npair,
    word 1 0 0,
    pb * gmu,
    npair,
    gmu * gmu,
    (gmu * gmu) * (gmu * gmu),
    ((gmu * gmu) * (gmu * gmu)) * ((gmu * gmu) * (gmu * gmu)),
    layers * (((gmu * gmu) * (gmu * gmu)) * ((gmu * gmu) * (gmu * gmu))),
    (digestScalars cvF).1,
    (digestScalars cvF).2,
    curF,
    rowF,
    word 1 0 0,
    (word 1 0 0) + gmu,
    word 1 0 0,
    (digestScalars cvF).1,
    (digestScalars cvF).2,
    curF,
    vF0,
    vF1,
    vF2]

def vbgP0 : List Stmt :=
  [.atom (.const (.n 5) (word 4 0 0)),
    .atom (.mul (.n 6) (.n 3) (.n 5)),
    .atom (.mul (.n 7) (.n 6) (.n 6)),
    .atom (.mul (.n 8) (.n 7) (.n 7)),
    .atom (.mul (.n 9) (.n 8) (.n 8)),
    .atom (.hint (.allocDyn (.n 10) (.n 9))),
    .atom (.hint (.alloc (.n 11) 3448)),
    .atom (.hint (.alloc (.n 12) 1640)),
    .atom (.const (.n 13) (word 4294967296 0 0)),
    .atom (.rangeCheck (.n 3) (.n 14) (.n 15) (.n 16) (.n 13)),
    .atom (.copy (.n 17) (.n 0)),
    .atom (.copy (.n 18) (.n 1))]

def vbgP1 : List Stmt :=
  [.atom (.const (.n 49) (word 0 0 0)),
    .atom (.add (.n 50) (.n 34) (.n 49)),
    .atom (.hint (.inverse (.n 50) (.n 51))),
    .atom (.assertNe (.n 50) (.n 51) (.n 52)),
    .atom (.load (.n 47) (.n 10) 0),
    .atom (.load (.n 48) (.n 10) 1),
    .atom (.const (.n 53) (word 4 0 0)),
    .atom (.mul (.n 54) (.n 2) (.n 53)),
    .atom (.load (.n 54) (.n 10) 2),
    .atom (.load (.n 19) (.n 10) 3),
    .atom (.load (.n 19) (.n 10) 4),
    .atom (.load (.n 34) (.n 10) 5),
    .atom (.load (.n 12) (.n 10) 6),
    .atom (.const (.n 55) (word 1 0 0)),
    .atom (.load (.n 55) (.n 10) 7),
    .atom (.hint (.alloc (.n 56) 33)),
    .atom (.hint (.alloc (.n 57) 33)),
    .atom (.const (.n 58) (word 1 0 0)),
    .atom (.load (.n 58) (.n 56) 0),
    .atom (.const (.n 59) (word 1 0 0)),
    .atom (.load (.n 59) (.n 57) 0),
    .atom (.const (.n 60) (word 1 0 0)),
    .atom (.load (.n 60) (.n 56) 1),
    .atom (.const (.n 61) (word 2 0 0)),
    .atom (.load (.n 61) (.n 57) 1),
    .atom (.const (.n 62) (word 2 0 0)),
    .atom (.load (.n 62) (.n 56) 2),
    .atom (.const (.n 63) (word 1 0 0)),
    .atom (.load (.n 63) (.n 57) 2),
    .atom (.const (.n 64) (word 2 0 0)),
    .atom (.load (.n 64) (.n 56) 3),
    .atom (.const (.n 65) (word 2 0 0)),
    .atom (.load (.n 65) (.n 57) 3),
    .atom (.const (.n 66) (word 4 0 0)),
    .atom (.load (.n 66) (.n 56) 4),
    .atom (.const (.n 67) (word 1 0 0)),
    .atom (.load (.n 67) (.n 57) 4),
    .atom (.const (.n 68) (word 4 0 0)),
    .atom (.load (.n 68) (.n 56) 5),
    .atom (.const (.n 69) (word 2 0 0)),
    .atom (.load (.n 69) (.n 57) 5),
    .atom (.const (.n 70) (word 8 0 0)),
    .atom (.load (.n 70) (.n 56) 6),
    .atom (.const (.n 71) (word 1 0 0)),
    .atom (.load (.n 71) (.n 57) 6),
    .atom (.const (.n 72) (word 8 0 0)),
    .atom (.load (.n 72) (.n 56) 7),
    .atom (.const (.n 73) (word 2 0 0)),
    .atom (.load (.n 73) (.n 57) 7),
    .atom (.const (.n 74) (word 16 0 0)),
    .atom (.load (.n 74) (.n 56) 8),
    .atom (.const (.n 75) (word 1 0 0)),
    .atom (.load (.n 75) (.n 57) 8),
    .atom (.const (.n 76) (word 16 0 0)),
    .atom (.load (.n 76) (.n 56) 9),
    .atom (.const (.n 77) (word 2 0 0)),
    .atom (.load (.n 77) (.n 57) 9),
    .atom (.const (.n 78) (word 32 0 0)),
    .atom (.load (.n 78) (.n 56) 10),
    .atom (.const (.n 79) (word 1 0 0)),
    .atom (.load (.n 79) (.n 57) 10),
    .atom (.const (.n 80) (word 32 0 0)),
    .atom (.load (.n 80) (.n 56) 11),
    .atom (.const (.n 81) (word 2 0 0)),
    .atom (.load (.n 81) (.n 57) 11),
    .atom (.const (.n 82) (word 64 0 0)),
    .atom (.load (.n 82) (.n 56) 12),
    .atom (.const (.n 83) (word 1 0 0)),
    .atom (.load (.n 83) (.n 57) 12),
    .atom (.const (.n 84) (word 64 0 0)),
    .atom (.load (.n 84) (.n 56) 13),
    .atom (.const (.n 85) (word 2 0 0)),
    .atom (.load (.n 85) (.n 57) 13),
    .atom (.const (.n 86) (word 128 0 0)),
    .atom (.load (.n 86) (.n 56) 14),
    .atom (.const (.n 87) (word 1 0 0)),
    .atom (.load (.n 87) (.n 57) 14),
    .atom (.const (.n 88) (word 128 0 0)),
    .atom (.load (.n 88) (.n 56) 15),
    .atom (.const (.n 89) (word 2 0 0)),
    .atom (.load (.n 89) (.n 57) 15),
    .atom (.const (.n 90) (word 256 0 0)),
    .atom (.load (.n 90) (.n 56) 16),
    .atom (.const (.n 91) (word 1 0 0)),
    .atom (.load (.n 91) (.n 57) 16),
    .atom (.const (.n 92) (word 256 0 0)),
    .atom (.load (.n 92) (.n 56) 17),
    .atom (.const (.n 93) (word 2 0 0)),
    .atom (.load (.n 93) (.n 57) 17),
    .atom (.const (.n 94) (word 512 0 0)),
    .atom (.load (.n 94) (.n 56) 18),
    .atom (.const (.n 95) (word 1 0 0)),
    .atom (.load (.n 95) (.n 57) 18),
    .atom (.const (.n 96) (word 512 0 0)),
    .atom (.load (.n 96) (.n 56) 19),
    .atom (.const (.n 97) (word 2 0 0)),
    .atom (.load (.n 97) (.n 57) 19),
    .atom (.const (.n 98) (word 1024 0 0)),
    .atom (.load (.n 98) (.n 56) 20),
    .atom (.const (.n 99) (word 1 0 0)),
    .atom (.load (.n 99) (.n 57) 20),
    .atom (.const (.n 100) (word 1024 0 0)),
    .atom (.load (.n 100) (.n 56) 21),
    .atom (.const (.n 101) (word 2 0 0)),
    .atom (.load (.n 101) (.n 57) 21),
    .atom (.const (.n 102) (word 2048 0 0)),
    .atom (.load (.n 102) (.n 56) 22),
    .atom (.const (.n 103) (word 1 0 0)),
    .atom (.load (.n 103) (.n 57) 22),
    .atom (.const (.n 104) (word 2048 0 0)),
    .atom (.load (.n 104) (.n 56) 23),
    .atom (.const (.n 105) (word 2 0 0)),
    .atom (.load (.n 105) (.n 57) 23),
    .atom (.const (.n 106) (word 4096 0 0)),
    .atom (.load (.n 106) (.n 56) 24),
    .atom (.const (.n 107) (word 1 0 0)),
    .atom (.load (.n 107) (.n 57) 24),
    .atom (.const (.n 108) (word 4096 0 0)),
    .atom (.load (.n 108) (.n 56) 25),
    .atom (.const (.n 109) (word 2 0 0)),
    .atom (.load (.n 109) (.n 57) 25),
    .atom (.const (.n 110) (word 8192 0 0)),
    .atom (.load (.n 110) (.n 56) 26),
    .atom (.const (.n 111) (word 1 0 0)),
    .atom (.load (.n 111) (.n 57) 26),
    .atom (.const (.n 112) (word 8192 0 0)),
    .atom (.load (.n 112) (.n 56) 27),
    .atom (.const (.n 113) (word 2 0 0)),
    .atom (.load (.n 113) (.n 57) 27),
    .atom (.const (.n 114) (word 16384 0 0)),
    .atom (.load (.n 114) (.n 56) 28),
    .atom (.const (.n 115) (word 1 0 0)),
    .atom (.load (.n 115) (.n 57) 28),
    .atom (.const (.n 116) (word 16384 0 0)),
    .atom (.load (.n 116) (.n 56) 29),
    .atom (.const (.n 117) (word 2 0 0)),
    .atom (.load (.n 117) (.n 57) 29),
    .atom (.const (.n 118) (word 32768 0 0)),
    .atom (.load (.n 118) (.n 56) 30),
    .atom (.const (.n 119) (word 1 0 0)),
    .atom (.load (.n 119) (.n 57) 30),
    .atom (.const (.n 120) (word 32768 0 0)),
    .atom (.load (.n 120) (.n 56) 31),
    .atom (.const (.n 121) (word 2 0 0)),
    .atom (.load (.n 121) (.n 57) 31),
    .atom (.const (.n 122) (word 65536 0 0)),
    .atom (.load (.n 122) (.n 56) 32),
    .atom (.const (.n 123) (word 1 0 0)),
    .atom (.load (.n 123) (.n 57) 32),
    .atom (.mul (.n 124) (.n 57) (.n 3)),
    .atom (.load (.n 125) (.n 124) 0),
    .atom (.const (.n 126) (word 1 0 0)),
    .atom (.add (.n 127) (.n 125) (.n 126))]

def vbgQ : List Stmt :=
  [.atom (.const (.n 287) (word 1 0 0)),
    .atom (.mul (.n 288) (.n 56) (.n 3)),
    .atom (.load (.n 289) (.n 288) 0),
    .atom (.add (.n 290) (.n 287) (.n 289)),
    .atom (.const (.n 291) (word 1 0 0)),
    .atom (.mul (.n 292) (.n 56) (.n 3)),
    .atom (.load (.n 293) (.n 292) 0),
    .callIf (.n 290) "__loop10" [.n 291, .n 293, .n 57, .n 3, .n 10, .n 11],
    .atom (.mul (.n 294) (.n 3) (.n 3)),
    .atom (.mul (.n 295) (.n 294) (.n 294)),
    .atom (.mul (.n 296) (.n 295) (.n 295)),
    .atom (.mul (.n 297) (.n 10) (.n 296)),
    .atom (.load (.n 298) (.n 297) 0),
    .atom (.load (.n 299) (.n 297) 1),
    .atom (.load (.n 300) (.n 297) 2),
    .atom (.load (.n 301) (.n 297) 6),
    .atom (.const (.n 302) (word 1 0 0)),
    .atom (.add (.n 303) (.n 302) (.n 3)),
    .atom (.const (.n 304) (word 1 0 0)),
    .callIf (.n 303) "__loop11" [.n 304, .n 3, .n 4, .n 301],
    .atom (.copy (.n 305) (.n 298)),
    .atom (.copy (.n 306) (.n 299)),
    .atom (.copy (.n 307) (.n 300)),
    .atom (.load (.n 308) (.n 297) 3),
    .atom (.load (.n 309) (.n 297) 4),
    .atom (.load (.n 310) (.n 297) 5)]

def vbgO0 : List Stmt :=
  [.atom (.load (.n 128) (.n 10) 0),
    .atom (.load (.n 129) (.n 10) 1)]

def vbgO1 : List Stmt :=
  [.atom (.load (.n 144) (.n 10) 2),
    .atom (.load (.n 145) (.n 10) 3),
    .atom (.load (.n 146) (.n 10) 4),
    .atom (.load (.n 147) (.n 10) 5),
    .atom (.mul (.n 148) (.n 143) (.n 147)),
    .atom (.add (.n 149) (.n 146) (.n 148)),
    .atom (.mul (.n 150) (.n 143) (.n 149)),
    .atom (.add (.n 151) (.n 145) (.n 150)),
    .atom (.load (.n 152) (.n 10) 6),
    .atom (.const (.n 153) (word 1099511627776 0 0)),
    .atom (.mul (.n 154) (.n 152) (.n 153))]

def vbgO2 : List Stmt :=
  [.atom (.mul (.n 251) (.n 234) (.n 250)),
    .atom (.const (.n 252) (word 0 0 0)),
    .atom (.mul (.n 253) (.n 143) (.n 252)),
    .atom (.add (.n 254) (.n 251) (.n 253)),
    .atom (.mul (.n 255) (.n 202) (.n 218)),
    .atom (.mul (.n 256) (.n 143) (.n 254)),
    .atom (.add (.n 257) (.n 255) (.n 256)),
    .atom (.mul (.n 258) (.n 170) (.n 186)),
    .atom (.mul (.n 259) (.n 143) (.n 257)),
    .atom (.add (.n 260) (.n 258) (.n 259)),
    .atom (.assertEq (.n 151) (.n 260))]

def vbgO3 : List Stmt :=
  [.atom (.load (.n 274) (.n 154) 0),
    .atom (.load (.n 266) (.n 10) 8),
    .atom (.load (.n 267) (.n 10) 9),
    .atom (.const (.n 275) (word 64 0 0)),
    .atom (.mul (.n 276) (.n 144) (.n 275)),
    .atom (.load (.n 276) (.n 10) 10),
    .atom (.add (.n 277) (.n 170) (.n 186)),
    .atom (.mul (.n 278) (.n 274) (.n 277)),
    .atom (.add (.n 279) (.n 170) (.n 278)),
    .atom (.load (.n 279) (.n 10) 11),
    .atom (.add (.n 280) (.n 202) (.n 218)),
    .atom (.mul (.n 281) (.n 274) (.n 280)),
    .atom (.add (.n 282) (.n 202) (.n 281)),
    .atom (.load (.n 282) (.n 10) 12),
    .atom (.add (.n 283) (.n 234) (.n 250)),
    .atom (.mul (.n 284) (.n 274) (.n 283)),
    .atom (.add (.n 285) (.n 234) (.n 284)),
    .atom (.load (.n 285) (.n 10) 13),
    .atom (.load (.n 154) (.n 10) 14),
    .atom (.const (.n 286) (word 2 0 0)),
    .atom (.load (.n 286) (.n 10) 15)]

def vbgOF : List Stmt :=
  (fsNextT (.n 135) (.n 136) (.n 144) 0 155 ++ [.atom (.copy (.n 170) (.n 155))]) ++
    (fsNextT (.n 168) (.n 169) (.n 144) 1 171 ++ [.atom (.copy (.n 186) (.n 171))]) ++
    (fsNextT (.n 184) (.n 185) (.n 144) 2 187 ++ [.atom (.copy (.n 202) (.n 187))]) ++
    (fsNextT (.n 200) (.n 201) (.n 144) 3 203 ++ [.atom (.copy (.n 218) (.n 203))]) ++
    (fsNextT (.n 216) (.n 217) (.n 144) 4 219 ++ [.atom (.copy (.n 234) (.n 219))]) ++
    (fsNextT (.n 232) (.n 233) (.n 144) 5 235 ++ [.atom (.copy (.n 250) (.n 235))])

theorem find_vbg : coreProgram.find? "verify_bus_gkr" = some Data.core10 := find_verify_bus_gkr

theorem vbg_body : Fn.body Data.core10 = vbgP0 ++ (fsNextT (.n 17) (.n 18) (.n 2) 0 19 ++
    (fsNextT (.n 32) (.n 33) (.n 2) 1 34 ++ (vbgP1 ++ (.ite (.n 127) [] (vbgO0 ++ (squeezeT (.n 128)
      (.n 129) 130 ++ (vbgO1 ++ (vbgOF ++ (vbgO2 ++ (squeezeT (.n 248) (.n 249) 261 ++ vbgO3)))))) ::
      (vbgQ ++ [.ret [.n 305, .n 306, .n 307, .n 308, .n 309, .n 310]]))))) :=
  stmtsEqb_sound (by decide +kernel)

theorem gkrFsv_obs1 (x : E) (cv : Digest) : gkrFsv x cv 13 = (digestScalars (obsCv cv x)).1 := rfl

theorem gkrFsv_obs2 (x : E) (cv : Digest) : gkrFsv x cv 14 = (digestScalars (obsCv cv x)).2 := rfl

/-- `pair_bounds`: `g^(d/2)`. -/
def vbgPb : List E := [word 1 0 0, word 1 0 0, word 2 0 0, word 2 0 0, word 4 0 0, word 4 0 0, word 8 0 0, word 8 0 0, word 16 0 0, word 16 0 0, word 32 0 0, word 32 0 0, word 64 0 0, word 64 0 0, word 128 0 0, word 128 0 0, word 256 0 0, word 256 0 0, word 512 0 0, word 512 0 0, word 1024 0 0, word 1024 0 0, word 2048 0 0, word 2048 0 0, word 4096 0 0, word 4096 0 0, word 8192 0 0, word 8192 0 0, word 16384 0 0, word 16384 0 0, word 32768 0 0, word 32768 0 0, word 65536 0 0]

/-- `depth_shift`: `g^(d%2)`. -/
def vbgDs : List E := [word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0, word 2 0 0, word 1 0 0]

/-- The odd layer's words: its six children, its check, the next row's challenge, the layer `1`
slots. -/
structure VbgOdd (rd : Reader) (layers pts cur : E) (cv : Digest) (x0 cnt : E) (oes : ℕ → E) : Prop where
  hc : ∀ i < 6, LoadHolds rd (cur * word 4 0 0) i (oes i)
  chk : x0 + (challengeOf (sqCv (vbgCv0 cv x0 cnt))) * (x0 + (challengeOf (sqCv (vbgCv0 cv x0 cnt))) * cnt) =
    oes 0 * oes 1 + (challengeOf (sqCv (vbgCv0 cv x0 cnt))) * (oes 2 * oes 3 + (challengeOf (sqCv (vbgCv0 cv x0 cnt))) * (oes 4 * oes 5))
  hrow : LoadHolds rd (pts * word 1099511627776 0 0) 0 (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6)))
  hl1 : ∀ k < 8, LoadHolds rd layers (8 + k) ([(digestScalars (sqCv (l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6))).1, (digestScalars (sqCv (l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6))).2, cur * word 4 0 0 * word 64 0 0, oes 0 + (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6))) * (oes 0 + oes 1), oes 2 + (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6))) * (oes 2 + oes 3), oes 4 + (challengeOf (sqCv (l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6))) * (oes 4 + oes 5), pts * word 1099511627776 0 0, word 2 0 0].getD k 0)

/-- The honest valuation of `verify_bus_gkr`'s body. -/
noncomputable def vbgσ (zeta fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 : E)
    (cv cvF : Digest) (oes : ℕ → E) : Val :=
  setl (Val.ofArgs [fs0, fs1, cur, gmu, zeta]) 5 (vbgVals fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem vbg_P1 {C : CallRel} {rd : Reader} {fs0 fs1 cur gmu zeta layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt
    shE npair curF rowF vF0 vF1 vF2 : E} {cv cvF : Digest} {oes : ℕ → E} {next : Prop} {kret : List E → Prop}
    (hne : (cnt + word 0 0 0) * cinv = 1)
    (hl0 : ∀ k < 8, LoadHolds rd layers k ([(digestScalars (vbgCv0 cv x0 cnt)).1,
      (digestScalars (vbgCv0 cv x0 cnt)).2, cur * word 4 0 0, x0, x0, cnt, pts, word 1 0 0].getD k 0))
    (hpb : ∀ k < 33, LoadHolds rd pb k (vbgPb.getD k 0))
    (hdt : ∀ k < 33, LoadHolds rd dsb k (vbgDs.getD k 0))
    (hsh : LoadHolds rd (dsb * gmu) 0 shE) (hn : next) :
    Stmt.HoldsList C rd (vbgσ zeta fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes) vbgP1 next kret := by
  set σ := vbgσ zeta fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes with hσ
  simp only [vbgP1, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨rfl, rfl, trivial, ⟨hne.symm, rfl⟩, (by rw [show σ (.n 47) = (digestScalars (vbgCv0 cv x0 cnt)).1 from gkrFsv_obs1 _ _]; exact hl0 0 (by norm_num)), (by rw [show σ (.n 48) = (digestScalars (vbgCv0 cv x0 cnt)).2 from gkrFsv_obs2 _ _]; exact hl0 1 (by norm_num)), rfl, rfl, (by have h := hl0 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, (by have h := hl0 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), trivial, trivial, rfl, (by have h := hpb 0 (by norm_num); simp only [List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 0 (by norm_num); simp only [List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 8 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 8 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 9 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 9 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 10 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 10 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 11 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 11 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 12 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 12 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 13 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 13 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 14 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 14 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 15 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 15 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 16 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 16 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 17 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 17 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 18 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 18 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 19 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 19 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 20 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 20 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 21 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 21 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 22 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 22 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 23 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 23 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 24 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 24 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 25 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 25 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 26 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 26 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 27 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 27 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 28 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 28 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 29 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 29 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 30 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 30 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 31 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 31 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, (by have h := hpb 32 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgPb] at h; exact h), rfl, (by have h := hdt 32 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero, vbgDs] at h; exact h), rfl, hsh, rfl, rfl, ?_⟩
  exact hn

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_bus_gkr`'s body holds** at its honest values, on a memory holding the words it loads,
for any relation its two loops hold of. -/
theorem vbg_holds {C : CallRel} {rd : Reader} {fs0 fs1 cur gmu zeta layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt
    shE npair curF rowF vF0 vF1 vF2 : E} {cv cvF : Digest} {oes : ℕ → E}
    (hfs : (fs0, fs1) = digestScalars cv)
    (hrc1 : LoadHolds rd gmu 0 rct1) (hrc2 : LoadHolds rd rcy 0 rct2) (hrck : word 4294967296 0 0 = gmu * rcy)
    (hx0 : LoadHolds rd cur 0 x0) (hcnt : LoadHolds rd cur 1 cnt) (hne : (cnt + word 0 0 0) * cinv = 1)
    (hl0 : ∀ k < 8, LoadHolds rd layers k ([(digestScalars (vbgCv0 cv x0 cnt)).1,
      (digestScalars (vbgCv0 cv x0 cnt)).2, cur * word 4 0 0, x0, x0, cnt, pts, word 1 0 0].getD k 0))
    (hpb : ∀ k < 33, LoadHolds rd pb k (vbgPb.getD k 0))
    (hdt : ∀ k < 33, LoadHolds rd dsb k (vbgDs.getD k 0))
    (hsh : LoadHolds rd (dsb * gmu) 0 shE) (hK127 : IsInK (shE + word 1 0 0))
    (hodd : shE + word 1 0 0 ≠ 0 → VbgOdd rd layers pts cur cv x0 cnt oes)
    (hnp : LoadHolds rd (pb * gmu) 0 npair) (hK290 : IsInK (word 1 0 0 + npair))
    (h10 : word 1 0 0 + npair ≠ 0 → C "__loop10" [word 1 0 0, npair, dsb, gmu, layers, rounds] [])
    (hlF : ∀ k < 7, LoadHolds rd (layers * gmu ^ 8) k ([(digestScalars cvF).1, (digestScalars cvF).2, curF,
      vF0, vF1, vF2, rowF].getD k 0))
    (hK303 : IsInK (word 1 0 0 + gmu))
    (h11 : word 1 0 0 + gmu ≠ 0 → C "__loop11" [word 1 0 0, gmu, zeta, rowF] []) :
    Stmt.HoldsList C rd (setl (Val.ofArgs [fs0, fs1, cur, gmu, zeta]) 5 (vbgVals fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes)) (Fn.body Data.core10) False
      (fun rs => rs = [(digestScalars cvF).1, (digestScalars cvF).2, curF, vF0, vF1, vF2]) := by
  set σ := setl (Val.ofArgs [fs0, fs1, cur, gmu, zeta]) 5 (vbgVals fs0 fs1 cur gmu layers rounds pts pb dsb rcy rct1 rct2 cinv x0 cnt shE npair curF rowF vF0 vF1 vF2 cv cvF oes) with hσ
  have e297 : σ (.n 297) = layers * gmu ^ 8 := by show layers * _ = _; ring
  have hQ : Stmt.HoldsList C rd σ (vbgQ ++ [.ret [.n 305, .n 306, .n 307, .n 308, .n 309, .n 310]]) False
      (fun rs => rs = [(digestScalars cvF).1, (digestScalars cvF).2, curF, vF0, vF1, vF2]) := by
    rw [holdsList_append]
    simp only [vbgQ, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
    refine ⟨rfl, rfl, hnp, rfl, rfl, rfl, hnp, hK290, (fun h => by simp only [List.map_cons, List.map_nil]; exact h10 h), rfl, rfl, rfl, rfl, (by rw [e297]; have h := hlF 0 (by norm_num); simp only [List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, hK303, (fun h => by simp only [List.map_cons, List.map_nil]; exact h11 h), rfl, rfl, rfl, (by rw [e297]; have h := hlF 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by rw [e297]; have h := hlF 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), ?_⟩
    rfl
  rw [vbg_body]
  simp only [holdsList_append]
  simp only [vbgP0, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨rfl, rfl, rfl, rfl, rfl, trivial, trivial, trivial, rfl, ⟨hrc1, hrck, hrc2⟩, rfl, rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hx0, cv, hfs, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨hcnt, obsCv cv x0, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine vbg_P1 (zeta := zeta) hne hl0 hpb hdt hsh ?_
  refine ⟨hK127, fun _ => hQ, fun hne' => ?_⟩
  have OD := hodd hne'
  simp only [holdsList_append, vbgOF]
  simp only [vbgO0, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨(by rw [show σ (.n 128) = (digestScalars (vbgCv0 cv x0 cnt)).1 from gkrFsv_obs1 _ _]; exact hl0 0 (by norm_num)), (by rw [show σ (.n 129) = (digestScalars (vbgCv0 cv x0 cnt)).2 from gkrFsv_obs2 _ _]; exact hl0 1 (by norm_num)), ?_⟩
  rw [holds_squeezeT]
  refine ⟨⟨vbgCv0 cv x0 cnt, rfl, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [vbgO1, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨(by have h := hl0 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := hl0 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, rfl, (by have h := hl0 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨OD.hc 0 (by norm_num), l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 0, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨OD.hc 1 (by norm_num), l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 1, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨OD.hc 2 (by norm_num), l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 2, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨OD.hc 3 (by norm_num), l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 3, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨OD.hc 4 (by norm_num), l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 4, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  rw [holds_fsNextT]
  refine ⟨⟨OD.hc 5 (by norm_num), l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 5, rfl, fun k h1 h2 => by interval_cases k <;> rfl⟩, ?_⟩
  refine ⟨rfl, ?_⟩
  simp only [vbgO2, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (by rw [show σ (.n 260) = σ (.n 151) from by show (((oes 0)) * ((oes 1))) + (((sqVals (vbgCv0 cv x0 cnt) 13)) * ((((oes 2)) * ((oes 3))) + (((sqVals (vbgCv0 cv x0 cnt) 13)) * ((((oes 4)) * ((oes 5))) + (((sqVals (vbgCv0 cv x0 cnt) 13)) * (word 0 0 0)))))) = x0 + (((sqVals (vbgCv0 cv x0 cnt) 13)) * (x0 + (((sqVals (vbgCv0 cv x0 cnt) 13)) * cnt))); simp only [sqVals]; rw [OD.chk]; simp only [word_zero]; ring]; exact e_add_self _), ?_⟩
  rw [holds_squeezeT]
  refine ⟨⟨l10cv (sqCv (vbgCv0 cv x0 cnt)) oes 6, rfl, fun k hk => by interval_cases k <;> rfl⟩, ?_⟩
  simp only [vbgO3, Stmt.HoldsList, Stmt.Holds, Atom.Holds]
  refine ⟨OD.hrow, (by have h := OD.hl1 0 (by norm_num); simp only [List.getD_cons_zero] at h; exact h), (by have h := OD.hl1 1 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, (by have h := OD.hl1 2 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, (by have h := OD.hl1 3 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, (by have h := OD.hl1 4 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, rfl, rfl, (by have h := OD.hl1 5 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), (by have h := OD.hl1 6 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), rfl, (by have h := OD.hl1 7 (by norm_num); simp only [List.getD_cons_succ, List.getD_cons_zero] at h; exact h), ?_⟩
  exact hQ

end
end LeanVM.Guest.B1.VerifySub
