/-
  LeanVM.Guest.B1.Main.Template

  `main`'s body (G:3119-3316) as a template: its straight-line parts as the data writes them, the
  two forward branches exposed, and the leaf's deferred claim as two runs of zero stores.
-/

module

public import LeanVM.Guest.B1.Main.Children

/-!
# `main`'s body

`mainBody` is `Data.core0.body` (`core0_body`, by `decide +kernel` on `stmtsEqb`): the statements
before the direct DA branch (`mainPre`), the branch (`daBranch`, at `n_direct_da = g`), the
children (`mainMid`), the branch on `n_children = 1` (`leafT`, the leaf's deferred claim, or
`aggregate_claims`), and the own digest against the public input (`mainPost`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-- Statements 0 to 81: counts, range checks, the seed, the tables, the lists, the signer set, the
raw signatures. -/
def mainPre : List Stmt := [
    .atom (.hint (.witness "meta" (.stack [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]))),
    .atom (.const (.n 8) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 0) (.n 9) (.n 10) (.n 11) (.n 8)),
    .atom (.const (.n 12) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 1) (.n 13) (.n 14) (.n 15) (.n 12)),
    .atom (.const (.n 16) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 2) (.n 17) (.n 18) (.n 19) (.n 16)),
    .atom (.const (.n 20) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 3) (.n 21) (.n 22) (.n 23) (.n 20)),
    .atom (.const (.n 24) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 4) (.n 25) (.n 26) (.n 27) (.n 24)),
    .atom (.const (.n 28) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 5) (.n 29) (.n 30) (.n 31) (.n 28)),
    .atom (.const (.n 32) (word 65536 0 0)),
    .atom (.rangeCheck (.n 6) (.n 33) (.n 34) (.n 35) (.n 32)),
    .atom (.const (.n 36) (word 2 0 0)),
    .atom (.rangeCheck (.n 7) (.n 37) (.n 38) (.n 39) (.n 36)),
    .atom (.hint (.witness "da_meta" (.stack [.n 40, .n 41]))),
    .atom (.const (.n 42) (word 65536 0 0)),
    .atom (.rangeCheck (.n 40) (.n 43) (.n 44) (.n 45) (.n 42)),
    .atom (.const (.n 46) (word 139298 0 0)),
    .atom (.rangeCheck (.n 41) (.n 47) (.n 48) (.n 49) (.n 46)),
    .atom (.mul (.n 50) (.n 40) (.n 41)),
    .atom (.const (.n 51) (word 139298 0 0)),
    .atom (.rangeCheck (.n 50) (.n 52) (.n 53) (.n 54) (.n 51)),
    .atom (.mul (.n 55) (.n 0) (.n 1)),
    .atom (.mul (.n 56) (.n 3) (.n 4)),
    .atom (.mul (.n 57) (.n 55) (.n 56)),
    .atom (.mul (.n 58) (.n 57) (.n 50)),
    .atom (.const (.n 59) (word 9272771591053052074 0 0)),
    .atom (.rangeCheck (.n 58) (.n 60) (.n 61) (.n 62) (.n 59)),
    .atom (.hint (.witness "fs_seed" (.stack [.n 63, .n 64]))),
    .call "exponent_tables" [] [.n 65, .n 66],
    .atom (.mul (.n 67) (.n 50) (.n 50)),
    .atom (.mul (.n 68) (.n 67) (.n 67)),
    .atom (.hint (.allocDyn (.n 69) (.n 68))),
    .atom (.const (.n 70) (word 1 0 0)),
    .atom (.add (.n 71) (.n 70) (.n 50)),
    .atom (.const (.n 72) (word 1 0 0)),
    .callIf (.n 71) "__loop0" [.n 72, .n 50, .n 69],
    .call "da_list_digest" [.n 69, .n 40] [.n 73, .n 74],
    .atom (.mul (.n 75) (.n 55) (.n 55)),
    .atom (.mul (.n 76) (.n 75) (.n 75)),
    .atom (.hint (.allocDyn (.n 77) (.n 76))),
    .atom (.mul (.n 78) (.n 56) (.n 56)),
    .atom (.mul (.n 79) (.n 78) (.n 78)),
    .atom (.hint (.allocDyn (.n 80) (.n 79))),
    .call "claim_list_digest" [.n 77, .n 0, .n 66] [.n 81, .n 82],
    .call "claim_list_digest" [.n 80, .n 3, .n 66] [.n 83, .n 84],
    .atom (.const (.n 85) (word 1 0 0)),
    .atom (.add (.n 86) (.n 85) (.n 1)),
    .atom (.const (.n 87) (word 1 0 0)),
    .callIf (.n 86) "__loop1" [.n 87, .n 1, .n 77, .n 0],
    .atom (.const (.n 88) (word 1 0 0)),
    .atom (.add (.n 89) (.n 88) (.n 4)),
    .atom (.const (.n 90) (word 1 0 0)),
    .callIf (.n 89) "__loop2" [.n 90, .n 4, .n 80, .n 3],
    .atom (.mul (.n 91) (.n 0) (.n 3)),
    .atom (.mul (.n 92) (.n 91) (.n 40)),
    .atom (.const (.n 93) (word 1 0 0)),
    .atom (.add (.n 94) (.n 92) (.n 93)),
    .atom (.hint (.inverse (.n 94) (.n 95))),
    .atom (.assertNe (.n 94) (.n 95) (.n 96)),
    .atom (.const (.n 97) (word 13503953895743350343 11912009169889063794 0)),
    .atom (.const (.n 98) (word 11170449402626986623 6620516960021240235 0)),
    .atom (.const (.n 99) (word 64 4294967295 0)),
    .atom (.blake2s (.n 81) (.n 82) (.n 83) (.n 84) (.n 97) (.n 98) (.n 100) (.n 101) (.n 99)),
    .atom (.hint (.alloc (.n 102) 2)),
    .atom (.load (.n 100) (.n 102) 0),
    .atom (.load (.n 101) (.n 102) 1),
    .atom (.hint (.allocDyn (.n 103) (.n 58))),
    .atom (.mul (.n 104) (.n 103) (.n 57)),
    .atom (.const (.n 105) (word 1 0 0)),
    .atom (.add (.n 106) (.n 105) (.n 2)),
    .atom (.const (.n 107) (word 1 0 0)),
    .callIf (.n 106) "__loop3" [.n 107, .n 2, .n 55, .n 103, .n 77],
    .atom (.const (.n 108) (word 1 0 0)),
    .atom (.add (.n 109) (.n 108) (.n 5)),
    .atom (.const (.n 110) (word 1 0 0)),
    .callIf (.n 109) "__loop4" [.n 110, .n 5, .n 56, .n 103, .n 55, .n 2, .n 80],
    .atom (.const (.n 111) (word 2 0 0)),
    .atom (.add (.n 112) (.n 7) (.n 111))]

/-- The direct DA branch. -/
def daBranch : List Stmt := [
    .call "da_verify" [.n 66] [.n 113, .n 114, .n 115, .n 116],
    .atom (.mul (.n 117) (.n 2) (.n 5)),
    .call "cover_da_root" [.n 69, .n 104, .n 50, .n 117] [.n 118, .n 119, .n 120, .n 121],
    .atom (.assertEq (.n 113) (.n 118)),
    .atom (.assertEq (.n 114) (.n 119)),
    .atom (.assertEq (.n 115) (.n 120)),
    .atom (.assertEq (.n 116) (.n 121))]

/-- Statements 83 to 119: the children's buffers, their loop, the count, `defer_stmt`. -/
def mainMid : List Stmt := [
    .atom (.mul (.n 122) (.n 6) (.n 6)),
    .atom (.hint (.allocDyn (.n 123) (.n 122))),
    .atom (.mul (.n 124) (.n 6) (.n 6)),
    .atom (.mul (.n 125) (.n 124) (.n 6)),
    .atom (.mul (.n 126) (.n 125) (.n 125)),
    .atom (.mul (.n 127) (.n 126) (.n 126)),
    .atom (.mul (.n 128) (.n 127) (.n 6)),
    .atom (.mul (.n 129) (.n 128) (.n 128)),
    .atom (.mul (.n 130) (.n 129) (.n 129)),
    .atom (.mul (.n 131) (.n 130) (.n 6)),
    .atom (.mul (.n 132) (.n 131) (.n 131)),
    .atom (.hint (.allocDyn (.n 133) (.n 132))),
    .atom (.mul (.n 134) (.n 6) (.n 6)),
    .atom (.mul (.n 135) (.n 134) (.n 6)),
    .atom (.mul (.n 136) (.n 135) (.n 135)),
    .atom (.mul (.n 137) (.n 136) (.n 136)),
    .atom (.mul (.n 138) (.n 137) (.n 6)),
    .atom (.mul (.n 139) (.n 138) (.n 138)),
    .atom (.mul (.n 140) (.n 139) (.n 139)),
    .atom (.mul (.n 141) (.n 140) (.n 6)),
    .atom (.hint (.allocDyn (.n 142) (.n 141))),
    .atom (.const (.n 143) (word 2 0 0)),
    .atom (.mul (.n 144) (.n 6) (.n 143)),
    .atom (.hint (.allocDyn (.n 145) (.n 144))),
    .atom (.mul (.n 146) (.n 2) (.n 5)),
    .atom (.mul (.n 147) (.n 146) (.n 7)),
    .atom (.load (.n 147) (.n 145) 0),
    .atom (.const (.n 148) (word 1 0 0)),
    .atom (.add (.n 149) (.n 148) (.n 6)),
    .atom (.const (.n 150) (word 1 0 0)),
    .callIf (.n 149) "__loop5" [.n 150, .n 6, .n 145, .n 77, .n 103, .n 55, .n 66, .n 80, .n 56, .n 142, .n 69, .n 104, .n 50, .n 63, .n 64, .n 123, .n 65, .n 133],
    .atom (.mul (.n 151) (.n 145) (.n 6)),
    .atom (.load (.n 152) (.n 151) 0),
    .atom (.assertEq (.n 152) (.n 58)),
    .atom (.hint (.alloc (.n 153) 53)),
    .atom (.const (.n 154) (word 1 0 0)),
    .atom (.add (.n 155) (.n 6) (.n 154))]

/-- Zero stores `defer_stmt[o + k] = 0`, `k < n`, the zeros at `b + k`. -/
def zeroStores (b o : ℕ) (k : ℕ) : List Stmt :=
  [.atom (.const (.n (b + k)) (word 0 0 0)), .atom (.load (.n (b + k)) (.n 153) (o + k))]

/-- The leaf's deferred claim: the points zero, the values hinted. -/
def leafT : List Stmt :=
  .atom (.hint (.witness "leaf_defer" (.stack [.n 156, .n 157, .n 158]))) ::
    (((List.range 22).map (zeroStores 159 0)).flatten ++ [.atom (.load (.n 156) (.n 153) 22)] ++
      ((List.range 28).map (zeroStores 181 23)).flatten ++
      [.atom (.load (.n 157) (.n 153) 51), .atom (.load (.n 158) (.n 153) 52)])

/-- The batching branch. -/
def aggT : List Stmt := [.call "aggregate_claims" [.n 6, .n 123, .n 133, .n 142, .n 153] []]

/-- Statements 121 to 130: the own digest against the public input. -/
def mainPost : List Stmt := [
    .call "statement_digest" [.n 63, .n 64, .n 102, .n 73, .n 74, .n 153] [.n 209, .n 210],
    .atom (.const (.n 211) (word 1 0 0)),
    .atom (.load (.n 212) (.n 211) 0),
    .atom (.assertEq (.n 212) (.n 209)),
    .atom (.const (.n 213) (word 1 0 0)),
    .atom (.const (.n 214) (word 2 0 0)),
    .atom (.mul (.n 215) (.n 213) (.n 214)),
    .atom (.load (.n 216) (.n 215) 0),
    .atom (.assertEq (.n 216) (.n 210)),
    .ret []]

/-- `main`'s body. -/
def mainBody : List Stmt :=
  mainPre ++ .ite (.n 112) daBranch [] :: (mainMid ++ .ite (.n 155) leafT aggT :: mainPost)

theorem core0_body : Fn.body Data.core0 = mainBody := stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Main
