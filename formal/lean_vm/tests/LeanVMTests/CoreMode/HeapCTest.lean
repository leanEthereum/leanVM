/-
  LeanVMTests.CoreMode.HeapCTest

  The heap check with calls and loops on hand-written certificates: two loop helpers and a caller
  as the guest had them (frozen), and small functions for returned words, runs consumed and a dispatch.
-/

import LeanVM.Guest.CoreMode.HeapC
import LeanVM.Guest.Data.Pows

/-!
# Tests of `heapOkC`

Certificates written by hand, each checked by the kernel (`decide +kernel`), and a wrong witness
rejected.

* `__loop0_verify_bus_gkr` (`verify_bus_gkr_loop0`): reads `p3·i` (its own `preR`, at its counter by the
  termination fact), stores at `p2·i` (its `postR`, accumulated), its tail call's `preR` one further
  (the shifted lower bound).
* `__loop0_da_pad` (`da_pad_loop0`): two accumulated runs of stride 2 over `p2·p3²`.
* `opening_round`: reads `p5[0..4]` (preconditions), calls `grind_check__L7` (empty signature here),
  stores `p8[0]`, `p9[0]`, `p9[1]` (its guarantees).
* `mk`, `useMk`: a guarantee over a returned word, read by the caller after the call; `useMk2`, the
  same through a `dispatch` of two arms.
* `fill`, `useFill`: a loop's accumulated run `p·g^j`, `j < e(n)`, read by its caller at the constant
  index `3` (a residual `3 < e(n)`) and passed whole to a second loop's `preR`; `useFillIf`, the loop
  entered by a `callIf` whose guard is `g^0 + n`, its run pushed (`callIfR`); `useFillX`, reads at the
  indices `x` and `x·g^3` of the run, by residuals on a value and on a monomial (`idx`, `CIdx.mono`).
* `off2`, `useOff2`, `useOff2D`: a returned word `p·g^2` (`retM`), read through by the caller, after a
  call and after a `dispatch`; `hvf`: a word stored, read back and read through (`hv`); `divf`: a
  quotient by `g` (`divs`).
* `rdg`, `useG`: reads through a cursor into a caller's object, the object a precondition over two ghost
  slots, named by the caller (`ghosts`, `gargs`); `rdl`, the same in a loop, its tail call naming its own
  ghosts.
* `joinf`, `joinm`: a cell stored by every branch of an `if` or every arm of a `match` falling through,
  read after it (joins).
* `useDp`: a pointer fact every arm of a `dispatch` guarantees, read through after it.
* `useCd`: two dispatches on one selector, arm `j` of the second needing what arm `j` of the first wrote
  (guarantees under a selector).
* `useM`: a run of stride `1` met by its two residue runs of stride `2` (`mrg`).
* `mkv`, `useV`: a word stored at a guaranteed cell, named at return (`postV`) and read back by the caller.
* `rdd`, `useD`: a callee's ghost named by the word at a cell its caller never loads (`ders`, value `DB`).
* `catk`: a run split at a symbolic index (`catM`); `useME`: a merge whose root is given by an equation
  (`mrgE`); `useAb`: a block every arm of a `dispatch` writes up to its index (`ab`); `pubRd`: constant
  preconditions (the public input); `fillP`, `useFillP`: a loop's accumulated pointer run, consumed.
* `mkq`, `useq`, `catq`: a run at the word a callee stores at a cell (`postQ`), read by the caller after it loads
  the cell; the run's second part split again (nested `catM`).

* `rdw`: a read through the word at a parameter's cell, a ghost's by the signature (`gw`).
-/

namespace LeanVM.Guest.CoreMode.Test

open LeanVM.Guest LeanVM.Guest.Core

section

/-! ## Loop helpers of the guest -/

/-- `verify_bus_gkr_loop0` as the guest had it, frozen: no guest edit changes the test. -/
def loopCopy : Fn where
  name := "__loop0_verify_bus_gkr"
  params := [.n 0, .n 1, .n 2, .n 3]
  body := [
    .atom (.mul (.n 4) (.n 3) (.n 0)),
    .atom (.load (.n 5) (.n 4) 0),
    .atom (.mul (.n 6) (.n 2) (.n 0)),
    .atom (.load (.n 5) (.n 6) 0),
    .atom (.const (.n 7) (word 2 0)),
    .atom (.mul (.n 8) (.n 0) (.n 7)),
    .atom (.add (.n 9) (.n 8) (.n 1)),
    .atom (.const (.n 10) (word 2 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)),
    .callIf (.n 9) "__loop0_verify_bus_gkr" [.n 11, .n 1, .n 2, .n 3],
    .ret []]

/-- `da_pad_loop0` as the guest had it, frozen: no guest edit changes the test. -/
def loopPad : Fn where
  name := "__loop0_da_pad"
  params := [.n 0, .n 1, .n 2, .n 3]
  body := [
    .atom (.mul (.n 4) (.n 3) (.n 3)),
    .atom (.mul (.n 5) (.n 2) (.n 4)),
    .atom (.mul (.n 6) (.n 0) (.n 0)),
    .atom (.mul (.n 7) (.n 5) (.n 6)),
    .atom (.const (.n 8) (word 8002054802297438051 4108169256045952147)),
    .atom (.load (.n 8) (.n 7) 0),
    .atom (.const (.n 9) (word 12830724869163462953 1721925254677230945)),
    .atom (.load (.n 9) (.n 7) 1),
    .atom (.const (.n 10) (word 2 0)),
    .atom (.mul (.n 11) (.n 0) (.n 10)),
    .atom (.add (.n 12) (.n 11) (.n 1)),
    .atom (.const (.n 13) (word 2 0)),
    .atom (.mul (.n 14) (.n 0) (.n 13)),
    .callIf (.n 12) "__loop0_da_pad" [.n 14, .n 1, .n 2, .n 3],
    .ret []]

/-- `opening_round` as the guest had it, frozen: no guest edit changes the test. -/
def openingRound : Fn where
  name := "opening_round"
  params := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9]
  body := (
    .atom (.copy (.n 10) (.n 0)) ::
    .atom (.copy (.n 11) (.n 1)) ::
    .atom (.copy (.n 12) (.n 2)) ::
    .atom (.copy (.n 13) (.n 3)) ::
    .atom (.copy (.n 14) (.n 4)) ::
    .atom (.load (.n 15) (.n 5) 0) ::
    .atom (.copy (.n 16) (.n 15)) ::
    .atom (.const (.n 17) (word 0 1)) ::
    .atom (.load (.n 18) (.n 5) 1) ::
    .atom (.copy (.n 19) (.n 18)) ::
    .atom (.const (.n 20) (word 0 1)) ::
    .atom (.load (.n 21) (.n 5) 2) ::
    .atom (.copy (.n 22) (.n 21)) ::
    .atom (.const (.n 23) (word 0 1)) ::
    .atom (.load (.n 24) (.n 5) 3) ::
    .atom (.copy (.n 25) (.n 24)) ::
    .atom (.const (.n 26) (word 0 1)) ::
    .atom (.keccak [.n 16, .n 17, .n 19, .n 20, .n 22, .n 23, .n 25, .n 26, .n 10, .n 11, .n 12, .n 13, .n 14] [.n 27, .n 28, .n 29, .n 30, .n 31, .n 32, .n 33, .n 34, .n 35, .n 36, .n 37, .n 38, .n 39] false false) ::
    .atom (.load (.n 40) (.n 5) 4) ::
    .atom (.copy (.n 41) (.n 40)) ::
    .atom (.const (.n 42) (word 0 4)) ::
    .atom (.const (.n 43) (word 1 0)) ::
    .atom (.const (.n 44) (word 0 0)) ::
    .atom (.const (.n 45) (word 0 0)) ::
    .atom (.const (.n 46) (word 0 0)) ::
    .atom (.const (.n 47) (word 0 0)) ::
    .atom (.keccak [.n 41, .n 42, .n 44, .n 44, .n 44, .n 45, .n 46, .n 47, .n 35, .n 36, .n 37, .n 38, .n 39] [.n 48, .n 49, .n 50, .n 51, .n 52, .n 53, .n 54, .n 55, .n 56, .n 57, .n 58, .n 59, .n 60] false false) ::
    .call "grind_check__L7" [.n 49, .n 7] [] ::
    .atom (.copy (.n 61) (.n 48)) ::
    .atom (.keccak [.n 44, .n 44, .n 44, .n 44, .n 44, .n 45, .n 46, .n 47, .n 56, .n 57, .n 58, .n 59, .n 60] [.n 62, .n 63, .n 64, .n 65, .n 66, .n 67, .n 68, .n 69, .n 70, .n 71, .n 72, .n 73, .n 74] false false) ::
    .atom (.copy (.n 75) (.n 62)) ::
    .atom (.load (.n 61) (.n 8) 0) ::
    .atom (.load (.n 61) (.n 9) 0) ::
    .atom (.load (.n 75) (.n 9) 1) ::
    .atom (.mul (.n 76) (.n 75) (.n 21)) ::
    .atom (.add (.n 77) (.n 15) (.n 76)) ::
    .atom (.add (.n 78) (.n 15) (.n 6)) ::
    .atom (.mul (.n 79) (.n 61) (.n 18)) ::
    .atom (.add (.n 80) (.n 78) (.n 79)) ::
    .atom (.add (.n 81) (.n 21) (.n 24)) ::
    .atom (.mul (.n 82) (.n 75) (.n 81)) ::
    .atom (.add (.n 83) (.n 80) (.n 82)) ::
    .atom (.mul (.n 84) (.n 61) (.n 83)) ::
    .atom (.add (.n 85) (.n 77) (.n 84)) ::
    .atom (.copy (.n 86) (.n 70)) ::
    .atom (.copy (.n 87) (.n 71)) ::
    .atom (.copy (.n 88) (.n 72)) ::
    .atom (.copy (.n 89) (.n 73)) ::
    .atom (.copy (.n 90) (.n 74)) ::
    .atom (.const (.n 91) (word 32 0)) ::
    .atom (.mul (.n 92) (.n 5) (.n 91)) ::
    .atom (.copy (.n 93) (.n 92)) ::
    .atom (.copy (.n 94) (.n 85)) ::
    .ret [.n 86, .n 87, .n 88, .n 89, .n 90, .n 93, .n 94] ::
    [])

/-- `__loop0_verify_bus_gkr`'s certificate. -/
def h7 : HCert where
  sig :=
    { preR := [⟨⟨[(3, 1)], 0⟩, 1, .val 0, .val 1⟩], postR := [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩],
      «term» := [(.val 0, .val 1)] }
  reads := [(5, [(4, 0, .run 0 [])])]
  res := []
  calls := [[.run 0 []]]
  rets := [[.ev 1]]

theorem loop7_ok : heapOkC Data.powTree (fun _ ↦ h7.sig) loopCopy h7 = true := by
  decide +kernel

/-- The point at the counter not written: the store's serial is `1`, not `0`. -/
theorem loop7_bad :
    heapOkC Data.powTree (fun _ ↦ h7.sig) loopCopy { h7 with rets := [[.ev 0]] } = false := by
  decide +kernel

/-- `__loop0_da_pad`'s certificate. -/
def h23 : HCert where
  sig :=
    { postR := [⟨⟨[(2, 1), (3, 2)], 0⟩, 2, .val 0, .val 1⟩, ⟨⟨[(2, 1), (3, 2)], 1⟩, 2, .val 0, .val 1⟩],
      «term» := [(.val 0, .val 1)] }
  reads := []
  res := []
  calls := [[]]
  rets := [[.ev 0, .ev 1]]

theorem loop23_ok : heapOkC Data.powTree (fun _ ↦ h23.sig) loopPad h23 = true := by
  decide +kernel

/-! ## A caller of the guest -/

/-- `opening_round`'s certificate, `grind_check__L7`'s signature taken empty. -/
def hOR : HCert where
  sig :=
    { pre := [⟨[(5, 1)], 0⟩, ⟨[(5, 1)], 1⟩, ⟨[(5, 1)], 2⟩, ⟨[(5, 1)], 3⟩, ⟨[(5, 1)], 4⟩],
      post := [⟨[(8, 1)], 0⟩, ⟨[(9, 1)], 0⟩, ⟨[(9, 1)], 1⟩] }
  reads := [(15, [(5, 0, .pre 0)]), (18, [(5, 1, .pre 1)]), (21, [(5, 2, .pre 2)]), (24, [(5, 3, .pre 3)]),
    (40, [(5, 4, .pre 4)])]
  res := []
  calls := [[]]
  rets := [[.ev 5, .ev 6, .ev 7]]

theorem openingRound_ok :
    heapOkC Data.powTree (fun g ↦ if g = "opening_round" then hOR.sig else .empty) openingRound hOR =
      true := by
  decide +kernel

/-! ## Returned words, dispatch -/

/-- Allocates a buffer, stores two words, returns it. -/
def mk : Fn where
  name := "mk"
  params := [.n 0]
  body := [.atom (.hint (.alloc (.n 1) 2)), .atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 1) 0),
    .atom (.load (.n 2) (.n 1) 1), .ret [.n 1]]

/-- `mk`'s certificate: its guarantees over the returned word (slot `1`). -/
def hMk : HCert where
  sig := { post := [⟨[(1, 1)], 0⟩, ⟨[(1, 1)], 1⟩] }
  reads := []
  res := []
  rets := [[.ev 0, .ev 1]]

/-- Calls `mk` and reads the second word of the buffer it returns. -/
def useMk : Fn where
  name := "useMk"
  params := [.n 0]
  body := [.call "mk" [.n 0] [.n 1], .atom (.load (.n 2) (.n 1) 1), .ret [.n 2]]

/-- `useMk`'s certificate: the read is the call's second guarantee (point serial `1`). -/
def hUseMk : HCert where
  sig := HSig.empty
  reads := [(2, [(1, 1, .ev 1)])]
  res := []
  calls := [[]]
  rets := [[]]

/-- The signatures of the synthetic functions. -/
def sigs (g : String) : HSig :=
  if g = "mk" then hMk.sig else if g = "fill" then hFill else if g = "readAll" then hReadAll
  else .empty
where
  hFill : HSig := { postR := [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩], «term» := [(.val 0, .val 1)] }
  hReadAll : HSig := { preR := [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩] }

theorem mk_ok : heapOkC Data.powTree sigs mk hMk = true := by decide +kernel

theorem useMk_ok : heapOkC Data.powTree sigs useMk hUseMk = true := by decide +kernel

/-- The second word is not the call's first guarantee. -/
theorem useMk_bad : heapOkC Data.powTree sigs useMk { hUseMk with reads := [(2, [(1, 1, .ev 0)])] } = false := by
  decide +kernel

/-- The same read after a dispatch of `mk` and `mk`: what both arms guarantee. -/
def useMk2 : Fn where
  name := "useMk2"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 1) ["mk", "mk"] [.n 0] [.n 2], .atom (.load (.n 3) (.n 2) 1), .ret [.n 3]]

theorem useMk2_ok :
    heapOkC Data.powTree sigs useMk2 { hUseMk with reads := [(3, [(2, 1, .ev 1)])] } = true := by
  decide +kernel

/-- A dispatch of `mk` and an arm `nope` that guarantees nothing, ruled out by the residual `e(x) < 1`
(`skip`): what `mk` guarantees is pushed. -/
def useMkX : Fn where
  name := "useMkX"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 1) ["mk", "nope"] [.n 0] [.n 2], .atom (.load (.n 3) (.n 2) 1), .ret [.n 3]]

theorem useMkX_ok :
    heapOkC Data.powTree sigs useMkX
      { hUseMk with reads := [(3, [(2, 1, .ev 1)])], res := [.lt (.val 1) (.num 1)], calls := [[.skip [0]]] } =
      true := by
  decide +kernel

/-- Without the arm ruled out, the meet is empty. -/
theorem useMkX_bad :
    heapOkC Data.powTree sigs useMkX
      { hUseMk with reads := [(3, [(2, 1, .ev 1)])], res := [.lt (.val 1) (.num 1)], calls := [[]] } = false := by
  decide +kernel

/-! ## A loop's run consumed -/

/-- Stores `0` at `p·i` for the counter `i` from its start to `n`. -/
def fill : Fn where
  name := "fill"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.mul (.n 3) (.n 2) (.n 0)), .atom (.const (.n 4) (word 0 0)), .atom (.load (.n 4) (.n 3) 0),
    .atom (.const (.n 5) (word 2 0)), .atom (.mul (.n 6) (.n 0) (.n 5)), .atom (.add (.n 7) (.n 6) (.n 1)),
    .atom (.const (.n 8) (word 2 0)), .atom (.mul (.n 9) (.n 0) (.n 8)), .callIf (.n 7) "fill" [.n 9, .n 1, .n 2],
    .ret []]

/-- `fill`'s certificate: the run `p·g^j`, `j` from the counter to the end, accumulated. -/
def hFill : HCert where
  sig := sigs.hFill
  reads := []
  res := []
  calls := [[]]
  rets := [[.ev 0]]

theorem fill_ok : heapOkC Data.powTree sigs fill hFill = true := by decide +kernel

/-- Reads `p·i` for the counter `i` from its start to `n`. -/
def readAll : Fn where
  name := "readAll"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.mul (.n 3) (.n 2) (.n 0)), .atom (.load (.n 4) (.n 3) 0),
    .atom (.const (.n 5) (word 2 0)), .atom (.mul (.n 6) (.n 0) (.n 5)), .atom (.add (.n 7) (.n 6) (.n 1)),
    .atom (.const (.n 8) (word 2 0)), .atom (.mul (.n 9) (.n 0) (.n 8)), .callIf (.n 7) "readAll" [.n 9, .n 1, .n 2],
    .ret []]

/-- `readAll`'s certificate: its read at its counter in its own `preR`, its tail call's one further. -/
def hReadAll : HCert where
  sig := { sigs.hReadAll with «term» := [(.val 0, .val 1)] }
  reads := [(4, [(3, 0, .run 0 [])])]
  res := []
  calls := [[.run 0 []]]
  rets := [[]]

theorem readAll_ok :
    heapOkC Data.powTree (fun g ↦ if g = "readAll" then hReadAll.sig else .empty) readAll hReadAll = true := by
  decide +kernel

/-- Fills `p` up to `n` from `g^0`, reads `p[3]`, then reads it all. -/
def useFill : Fn where
  name := "useFill"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 1 0)), .call "fill" [.n 2, .n 0, .n 1] [], .atom (.load (.n 3) (.n 1) 3),
    .call "readAll" [.n 2, .n 0, .n 1] [], .ret [.n 3]]

/-- `useFill`'s certificate: the read at index `3` in the run `fill` guarantees (run serial `0`), by the
residual `3 < e(n)`; `readAll`'s `preR` that very run. -/
def hUseFill : HCert where
  sig := HSig.empty
  reads := [(3, [(1, 3, .run 0 [0])])]
  res := [.lt (.num 3) (.val 0)]
  calls := [[], [.run 0 []]]
  rets := [[]]

theorem useFill_ok : heapOkC Data.powTree sigs useFill hUseFill = true := by decide +kernel

/-- The same read by a residual `sub` (the cell is one of the run's), and `readAll`'s `preR` by a `subR`. -/
theorem useFill_sub :
    heapOkC Data.powTree sigs useFill { hUseFill with
      reads := [(3, [(1, 3, .run 0 [0])])]
      res := [.sub ⟨[(1, 1)], 3⟩ ⟨⟨[(1, 1)], 0⟩, 1, .num 0, .val 0⟩,
        .subR ⟨⟨[(1, 1)], 0⟩, 1, .num 0, .val 0⟩ ⟨⟨[(1, 1)], 0⟩, 1, .num 0, .val 0⟩]
      calls := [[], [.run 0 [1]]] } = true := by
  decide +kernel

/-- A `sub` residual of another cell does not place it. -/
theorem useFill_subBad :
    heapOkC Data.powTree sigs useFill { hUseFill with
      reads := [(3, [(1, 3, .run 0 [0])])]
      res := [.sub ⟨[(1, 1)], 4⟩ ⟨⟨[(1, 1)], 0⟩, 1, .num 0, .val 0⟩] } = false := by
  decide +kernel

/-- `readAll`'s `preR` split at index `3` (`cat`): the points below by `pts`, the rest by the run. -/
theorem useFill_cat :
    heapOkC Data.powTree sigs useFill
      { hUseFill with calls := [[], [.cat 3, .pts, .run 0 [0], .run 0 [0], .run 0 [0], .run 0 [0]]] } = true := by
  decide +kernel

/-- Without the residual the index is not known in the run. -/
theorem useFill_bad : heapOkC Data.powTree sigs useFill { hUseFill with reads := [(3, [(1, 3, .run 0 [])])] } = false := by
  decide +kernel

/-- Enters `fill` through a `callIf` guarded by `c = g^0 + n`, then reads it all. -/
def useFillIf : Fn where
  name := "useFillIf"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 1 0)), .atom (.add (.n 3) (.n 2) (.n 0)), .callIf (.n 3) "fill" [.n 2, .n 0, .n 1],
    .call "readAll" [.n 2, .n 0, .n 1] [], .ret []]

/-- `useFillIf`'s certificate: the `callIf` pushes `fill`'s run, its bounds the guard's operands (run
serial `0`), which is `readAll`'s `preR`. -/
def hUseFillIf : HCert where
  sig := HSig.empty
  reads := []
  res := []
  calls := [[], [.run 0 []]]
  rets := [[]]

theorem useFillIf_ok : heapOkC Data.powTree sigs useFillIf hUseFillIf = true := by decide +kernel

/-- A guard that is not the run's bounds' sum pushes nothing. -/
theorem useFillIf_bad :
    heapOkC Data.powTree sigs { useFillIf with body := [.atom (.const (.n 2) (word 1 0)),
      .atom (.add (.n 3) (.n 2) (.n 1)), .callIf (.n 3) "fill" [.n 2, .n 0, .n 1], .call "readAll" [.n 2, .n 0, .n 1] [],
      .ret []] } hUseFillIf = false := by
  decide +kernel

/-- Fills `p` up to `n`, then reads `p[x]` and `p[x + 3]`. -/
def useFillX : Fn where
  name := "useFillX"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.const (.n 3) (word 1 0)), .call "fill" [.n 3, .n 0, .n 1] [], .atom (.mul (.n 4) (.n 1) (.n 2)),
    .atom (.load (.n 5) (.n 4) 0), .atom (.load (.n 6) (.n 4) 3), .ret []]

/-- `useFillX`'s certificate: both reads at an index of `fill`'s run (`idx`), by the residuals `e(x) < e(n)`
and `e(x·g^3) < e(n)` (a monomial bound, `CIdx.mono`). -/
def hUseFillX : HCert where
  sig := HSig.empty
  reads := [(5, [(4, 0, .run 0 [0])]), (6, [(4, 3, .run 0 [1])])]
  res := [.lt (.val 2) (.val 0), .lt (.mono ⟨[(2, 1)], 3⟩) (.val 0)]
  calls := [[]]
  rets := [[]]

theorem useFillX_ok : heapOkC Data.powTree sigs useFillX hUseFillX = true := by decide +kernel

/-- `e(x) < e(n)` does not place `x + 3`. -/
theorem useFillX_bad :
    heapOkC Data.powTree sigs useFillX { hUseFillX with reads := [(5, [(4, 0, .run 0 [0])]), (6, [(4, 3, .run 0 [0])])] } =
      false := by
  decide +kernel


/-! ## Returned words' monomials, words read back, divisions -/

/-- Returns `p·g^2`. -/
def off2 : Fn where
  name := "off2"
  params := [.n 0]
  body := [.atom (.const (.n 1) (word 4 0)), .atom (.mul (.n 2) (.n 0) (.n 1)), .ret [.n 2]]

/-- `off2`'s certificate: its returned word is `p·g^2` (`retM`). -/
def hOff2 : HCert where
  sig := { retM := [(0, ⟨[(0, 1)], 2⟩)] }
  reads := []
  res := []
  rets := [[]]

theorem off2_ok : heapOkC Data.powTree (fun _ ↦ .empty) off2 hOff2 = true := by decide +kernel

/-- The returned word is not `p·g^3`. -/
theorem off2_bad :
    heapOkC Data.powTree (fun _ ↦ .empty) off2 { hOff2 with sig := { hOff2.sig with retM := [(0, ⟨[(0, 1)], 3⟩)] } } =
      false := by
  decide +kernel

/-- Calls `off2` and reads the word after the one it returns, `p·g^3`. -/
def useOff2 : Fn where
  name := "useOff2"
  params := [.n 0]
  body := [.call "off2" [.n 0] [.n 1], .atom (.load (.n 2) (.n 1) 1), .ret []]

/-- `useOff2`'s certificate: the read is its precondition `p·g^3`, the returned word named by `off2`'s
`retM`. -/
def hUseOff2 : HCert where
  sig := { pre := [⟨[(0, 1)], 3⟩] }
  reads := [(2, [(1, 1, .pre 0)])]
  res := []
  calls := [[]]
  rets := [[]]

theorem useOff2_ok : heapOkC Data.powTree (fun g ↦ if g = "off2" then hOff2.sig else .empty) useOff2 hUseOff2 = true := by
  decide +kernel

/-- Without `off2`'s `retM` the returned word is its own base. -/
theorem useOff2_bad : heapOkC Data.powTree (fun _ ↦ .empty) useOff2 hUseOff2 = false := by decide +kernel

/-- The same through a `dispatch` of `off2` and `off2`: the monomial both arms give. -/
def useOff2D : Fn where
  name := "useOff2D"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 1) ["off2", "off2"] [.n 0] [.n 2], .atom (.load (.n 3) (.n 2) 1), .ret []]

theorem useOff2D_ok :
    heapOkC Data.powTree (fun g ↦ if g = "off2" then hOff2.sig else .empty) useOff2D
      { hUseOff2 with reads := [(3, [(2, 1, .pre 0)])] } = true := by
  decide +kernel

/-- Stores `p·g` at `p[0]`, reads `p[0]` back, then reads through the word read. -/
def hvf : Fn where
  name := "hvf"
  params := [.n 0]
  body := [.atom (.const (.n 1) (word 2 0)), .atom (.mul (.n 2) (.n 0) (.n 1)), .atom (.load (.n 2) (.n 0) 0),
    .atom (.load (.n 3) (.n 0) 0), .atom (.load (.n 4) (.n 3) 0), .ret []]

/-- `hvf`'s certificate: the read of `p[0]` is the store (event `0`), so its word is `p·g` (`hvs`), and the
read through it is the precondition `p·g`. -/
def hHvf : HCert where
  sig := { pre := [⟨[(0, 1)], 1⟩] }
  reads := [(3, [(0, 0, .ev 0)]), (4, [(3, 0, .pre 0)])]
  res := []
  rets := [[]]
  hvs := [3]

theorem hvf_ok : heapOkC Data.powTree (fun _ ↦ .empty) hvf hHvf = true := by decide +kernel

/-- Not listed, the word read is its own base. -/
theorem hvf_unlisted : heapOkC Data.powTree (fun _ ↦ .empty) hvf { hHvf with hvs := [] } = false := by decide +kernel

/-- The read through the word read is not `p·g^2`. -/
theorem hvf_bad :
    heapOkC Data.powTree (fun _ ↦ .empty) hvf { hHvf with sig := { pre := [⟨[(0, 1)], 2⟩] } } = false := by
  decide +kernel

/-- Computes `d = p·g^3`, divides it by `g` (`mul d q g`), reads `q[0]`. -/
def divf : Fn where
  name := "divf"
  params := [.n 0]
  body := [.atom (.const (.n 1) (word 8 0)), .atom (.mul (.n 2) (.n 0) (.n 1)), .atom (.const (.n 3) (word 2 0)),
    .atom (.mul (.n 2) (.n 4) (.n 3)), .atom (.load (.n 5) (.n 4) 0), .ret []]

/-- `divf`'s certificate: the quotient `q = p·g^2` (`divs`), its read the precondition `p·g^2`. -/
def hDivf : HCert where
  sig := { pre := [⟨[(0, 1)], 2⟩] }
  reads := [(5, [(4, 0, .pre 0)])]
  res := []
  rets := [[]]
  divs := [4]

theorem divf_ok : heapOkC Data.powTree (fun _ ↦ .empty) divf hDivf = true := by decide +kernel

/-- Not listed, the quotient is its own base. -/
theorem divf_bad : heapOkC Data.powTree (fun _ ↦ .empty) divf { hDivf with divs := [] } = false := by decide +kernel


/-! ## Pointer facts -/

/-- Allocates a buffer, writes its two words, stores its pointer at `p[0]`. -/
def mkp : Fn where
  name := "mkp"
  params := [.n 0]
  body := [.atom (.hint (.alloc (.n 1) 2)), .atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 1) 0),
    .atom (.load (.n 2) (.n 1) 1), .atom (.load (.n 1) (.n 0) 0), .ret []]

/-- `mkp`'s certificate: `p[0]` written, and a pointer to two written cells (`postP`, by the stored word,
`word`). -/
def hMkp : HCert where
  sig := { post := [⟨[(0, 1)], 0⟩], postP := [(⟨[(0, 1)], 0⟩, [0, 1])] }
  reads := []
  res := []
  rets := [[.ev 2, .word 2, .ev 0, .ev 1]]

theorem mkp_ok : heapOkC Data.powTree (fun _ ↦ .empty) mkp hMkp = true := by decide +kernel

/-- Calls `mkp`, loads `p[0]`, reads the second cell past it. -/
def usep : Fn where
  name := "usep"
  params := [.n 0]
  body := [.call "mkp" [.n 0] [], .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 1), .ret []]

/-- `usep`'s certificate: the call's `post` cell (point serial `0`), then its pointer fact (serial `1`). -/
def hUsep : HCert where
  sig := {}
  reads := [(1, [(0, 0, .ev 0)]), (2, [(1, 1, .pf 1)])]
  res := []
  calls := [[]]
  rets := [[]]

theorem usep_ok : heapOkC Data.powTree (fun g ↦ if g = "mkp" then hMkp.sig else .empty) usep hUsep = true := by
  decide +kernel

/-- The third cell past the pointer is not in the fact. -/
theorem usep_bad :
    heapOkC Data.powTree (fun g ↦ if g = "mkp" then hMkp.sig else .empty)
      { usep with body := [.call "mkp" [.n 0] [], .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 2),
        .ret []] } { hUsep with reads := [(1, [(0, 0, .ev 0)]), (2, [(1, 2, .pf 1)])] } = false := by
  decide +kernel

/-- Loads `p[2]` and reads the cell it points to, by its own pointer run `p[0..4)` (`prePR`). -/
def rdp : Fn where
  name := "rdp"
  params := [.n 0]
  body := [.atom (.load (.n 1) (.n 0) 2), .atom (.load (.n 2) (.n 1) 0), .ret []]

/-- `rdp`'s certificate: `p[2]` in its `preR`, the cell past it in its `prePR` (run serial `1`). -/
def hRdp : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 4⟩], prePR := [(⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 4⟩, [0])] }
  reads := [(1, [(0, 2, .run 0 [])]), (2, [(1, 0, .pfr 1 [])])]
  res := []
  rets := [[]]

theorem rdp_ok : heapOkC Data.powTree (fun _ ↦ .empty) rdp hRdp = true := by decide +kernel

/-- A caller meeting `rdp`'s pointer run cell by cell (`pts`): each `p[j]` holds a pointer to a written
cell, the words stored by the caller. -/
def callRdp : Fn where
  name := "callRdp"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 1) 0),
    .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 1) (.n 0) 1), .atom (.load (.n 1) (.n 0) 2),
    .atom (.load (.n 1) (.n 0) 3), .call "rdp" [.n 0] [], .ret []]

/-- `callRdp`'s certificate: `rdp`'s `preR` by its points, its `prePR` by `pts`, each cell's word `q`
(`word`) and `q[0]` written (event `0`). -/
def hCallRdp : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[.pts, .ev 1, .ev 2, .ev 3, .ev 4, .pts, .word 1, .ev 0, .word 2, .ev 0, .word 3, .ev 0, .word 4, .ev 0]]
  rets := [[]]

theorem callRdp_ok :
    heapOkC Data.powTree (fun g ↦ if g = "rdp" then hRdp.sig else .empty) callRdp hCallRdp = true := by
  decide +kernel

/-! ## Ghost words -/

/-- Reads `c[0]` and `c[1]`, `c` a cursor into a caller's object. -/
def rdg : Fn where
  name := "rdg"
  params := [.n 0]
  body := [.atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 0) 1), .ret []]

/-- `rdg`'s certificate: two ghosts (slots `1`, `2`; values `GB`, `GB + 1`), the object's base and bound,
its run `G₀·g^[0, e(G₁))` a precondition (`preR`); the reads in it by the residual "`c·g^[0, 2)` is in
the object" (`subR`). -/
def hRdg : HCert where
  sig := { preR := [⟨⟨[(1, 1)], 0⟩, 1, .num 0, .val 2⟩], ghosts := 2 }
  reads := [(1, [(0, 0, .run 0 [0])]), (2, [(0, 1, .run 0 [0])])]
  res := [.subR ⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 2⟩ ⟨⟨[(1048576, 1)], 0⟩, 1, .num 0, .val 1048577⟩]
  rets := [[]]

theorem rdg_ok : heapOkC Data.powTree (fun _ ↦ .empty) rdg hRdg = true := by decide +kernel

/-- One ghost only: the run's bound (slot `2`) names no word. -/
theorem rdg_one : heapOkC Data.powTree (fun _ ↦ .empty) rdg { hRdg with sig := { hRdg.sig with ghosts := 1 } } = false := by
  decide +kernel

/-- A body naming a ghost's value is refused. -/
theorem rdg_named :
    heapOkC Data.powTree (fun _ ↦ .empty) { rdg with body := [.atom (.load (.n 1) (.n 0) 0),
      .atom (.load (.n 1048576) (.n 0) 1), .ret []] } hRdg = false := by
  decide +kernel

/-- Calls `rdg` on the cursor `c` into its stream `s`, of bound `L`. -/
def useG : Fn where
  name := "useG"
  params := [.n 0, .n 1, .n 2]
  body := [.call "rdg" [.n 1] [], .ret []]

/-- `useG`'s certificate: its stream `s·g^[0, e(L))` a precondition, named as `rdg`'s ghosts (`gargs`):
`rdg`'s `preR` is then that very run. -/
def hUseG : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := []
  res := []
  calls := [[.run 0 []]]
  rets := [[]]
  gargs := [("rdg", [1], [⟨[(0, 1)], 0⟩, ⟨[(2, 1)], 0⟩])]

theorem useG_ok : heapOkC Data.powTree (fun g ↦ if g = "rdg" then hRdg.sig else .empty) useG hUseG = true := by
  decide +kernel

/-- Ghost words not named: `rdg`'s two ghosts get none. -/
theorem useG_none :
    heapOkC Data.powTree (fun g ↦ if g = "rdg" then hRdg.sig else .empty) useG { hUseG with gargs := [] } = false := by
  decide +kernel

/-- Ghost words named for another call (other arguments): none for this one. -/
theorem useG_key :
    heapOkC Data.powTree (fun g ↦ if g = "rdg" then hRdg.sig else .empty) useG
      { hUseG with gargs := [("rdg", [0], [⟨[(0, 1)], 0⟩, ⟨[(2, 1)], 0⟩])] } = false := by
  decide +kernel

/-- Another object (`c`'s own run): not a run in scope. -/
theorem useG_bad :
    heapOkC Data.powTree (fun g ↦ if g = "rdg" then hRdg.sig else .empty) useG
      { hUseG with gargs := [("rdg", [1], [⟨[(1, 1)], 0⟩, ⟨[(2, 1)], 0⟩])] } = false := by
  decide +kernel

/-- Reads `c·i` for the counter `i` from its start to `n`, `c` a cursor into a caller's object. -/
def rdl : Fn where
  name := "rdl"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.mul (.n 3) (.n 2) (.n 0)), .atom (.load (.n 4) (.n 3) 0),
    .atom (.const (.n 5) (word 2 0)), .atom (.mul (.n 6) (.n 0) (.n 5)), .atom (.add (.n 7) (.n 6) (.n 1)),
    .atom (.const (.n 8) (word 2 0)), .atom (.mul (.n 9) (.n 0) (.n 8)), .callIf (.n 7) "rdl" [.n 9, .n 1, .n 2],
    .ret []]

/-- `rdl`'s certificate: ghosts `G₀`, `G₁` (slots `3`, `4`), the object's run a precondition; the read at
the counter in it by the residual "`c·g^[e(i), e(n))` is in the object"; the tail call names its own
ghosts again. -/
def hRdl : HCert where
  sig := { preR := [⟨⟨[(3, 1)], 0⟩, 1, .num 0, .val 4⟩], «term» := [(.val 0, .val 1)], ghosts := 2 }
  reads := [(4, [(3, 0, .run 0 [0])])]
  res := [.subR ⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩ ⟨⟨[(1048576, 1)], 0⟩, 1, .num 0, .val 1048577⟩]
  calls := [[.run 0 []]]
  rets := [[]]
  gargs := [("rdl", [9, 1, 2], [⟨[(1048576, 1)], 0⟩, ⟨[(1048577, 1)], 0⟩])]

theorem rdl_ok : heapOkC Data.powTree (fun g ↦ if g = "rdl" then hRdl.sig else .empty) rdl hRdl = true := by
  decide +kernel

/-- The tail call's ghosts swapped: its precondition is another run. -/
theorem rdl_bad :
    heapOkC Data.powTree (fun g ↦ if g = "rdl" then hRdl.sig else .empty) rdl
      { hRdl with gargs := [("rdl", [9, 1, 2], [⟨[(1048577, 1)], 0⟩, ⟨[(1048576, 1)], 0⟩])] } = false := by
  decide +kernel

/-! ## Joins -/

/-- Stores `p[0]` in both branches of an `if` (and `p[1]` in the second), reads `p[0]` after. -/
def joinf : Fn where
  name := "joinf"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 0 0)),
    .ite (.n 1) [.atom (.load (.n 2) (.n 0) 0)] [.atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 2) (.n 0) 1)],
    .atom (.load (.n 3) (.n 0) 0), .ret []]

/-- `joinf`'s certificate: the read is the first branch's store (serial `0`), which the second branch also
makes. -/
def hJoinf : HCert where
  sig := {}
  reads := [(3, [(0, 0, .ev 0)])]
  res := []
  rets := [[]]

theorem joinf_ok : heapOkC Data.powTree (fun _ ↦ .empty) joinf hJoinf = true := by decide +kernel

/-- `p[1]`, stored in the second branch only, is not written after the join. -/
theorem joinf_bad :
    heapOkC Data.powTree (fun _ ↦ .empty)
      { joinf with body := [.atom (.const (.n 2) (word 0 0)),
        .ite (.n 1) [.atom (.load (.n 2) (.n 0) 0)] [.atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 2) (.n 0) 1)],
        .atom (.load (.n 3) (.n 0) 1), .ret []] }
      { hJoinf with reads := [(3, [(0, 1, .ev 2)])] } = false := by
  decide +kernel

/-- A `match` whose last arm returns: what the other two arms both store is written after it. -/
def joinm : Fn where
  name := "joinm"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 0 0)),
    .match_ (.n 1) [[.atom (.load (.n 2) (.n 0) 0)], [.atom (.load (.n 2) (.n 0) 1), .atom (.load (.n 2) (.n 0) 0)],
      [.ret []]],
    .atom (.load (.n 3) (.n 0) 0), .ret []]

/-- `joinm`'s certificate: the read is the first arm's store (serial `0`). -/
def hJoinm : HCert where
  sig := {}
  reads := [(3, [(0, 0, .ev 0)])]
  res := []
  rets := [[], []]

theorem joinm_ok : heapOkC Data.powTree (fun _ ↦ .empty) joinm hJoinm = true := by decide +kernel

/-- `p[1]`, stored in the second arm only, is not written after the `match`. -/
theorem joinm_bad :
    heapOkC Data.powTree (fun _ ↦ .empty)
      { joinm with body := [.atom (.const (.n 2) (word 0 0)),
        .match_ (.n 1) [[.atom (.load (.n 2) (.n 0) 0)], [.atom (.load (.n 2) (.n 0) 1), .atom (.load (.n 2) (.n 0) 0)],
          [.ret []]],
        .atom (.load (.n 3) (.n 0) 1), .ret []] }
      { hJoinm with reads := [(3, [(0, 1, .ev 1)])] } = false := by
  decide +kernel

/-- An `if` whose first branch returns: the second branch's store is written after it. -/
theorem joinr_ok :
    heapOkC Data.powTree (fun _ ↦ .empty)
      { joinf with body := [.atom (.const (.n 2) (word 0 0)), .ite (.n 1) [.ret []] [.atom (.load (.n 2) (.n 0) 1)],
        .atom (.load (.n 3) (.n 0) 1), .ret []] }
      { hJoinf with reads := [(3, [(0, 1, .ev 0)])], rets := [[], []] } = true := by
  decide +kernel

/-! ## A dispatch's pointer facts -/

/-- `usep` through a `dispatch` of `mkp` and `mkp`: the pointer fact both arms guarantee. -/
def useDp : Fn where
  name := "useDp"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 1) ["mkp", "mkp"] [.n 0] [], .atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 3) (.n 2) 1),
    .ret []]

/-- `useDp`'s certificate: the meet's `post` cell (point serial `0`), then its pointer fact (serial `1`). -/
def hUseDp : HCert where
  sig := {}
  reads := [(2, [(0, 0, .ev 0)]), (3, [(2, 1, .pf 1)])]
  res := []
  calls := [[]]
  rets := [[]]

/-- `mkp`'s signature, and `mkq`'s: `p[0]` written, no pointer fact. -/
def sigsP (g : String) : HSig :=
  if g = "mkp" then hMkp.sig else if g = "mkq" then { post := [⟨[(0, 1)], 0⟩] } else .empty

theorem useDp_ok : heapOkC Data.powTree sigsP useDp hUseDp = true := by decide +kernel

/-- An arm without the pointer fact: not in the meet. -/
theorem useDp_bad :
    heapOkC Data.powTree sigsP { useDp with body := [.dispatch (.n 1) ["mkp", "mkq"] [.n 0] [],
      .atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 3) (.n 2) 1), .ret []] } hUseDp = false := by
  decide +kernel

/-! ## Guarantees under a selector -/

/-- `wa` writes `p[0]`, `wb` `p[1]`; `ra` reads `p[0]`, `rb` `p[1]`. -/
def sigsC (g : String) : HSig :=
  if g = "wa" then { post := [⟨[(0, 1)], 0⟩] } else if g = "wb" then { post := [⟨[(0, 1)], 1⟩] }
  else if g = "ra" then { pre := [⟨[(0, 1)], 0⟩] } else if g = "rb" then { pre := [⟨[(0, 1)], 1⟩] } else .empty

/-- Dispatches `wa`/`wb` on `x`, then `ra`/`rb` on `x`: arm `j` of the second reads what arm `j` of the first
wrote, though the arms write nothing in common. -/
def useCd : Fn where
  name := "useCd"
  params := [.n 0, .n 1, .n 2]
  body := [.dispatch (.n 1) ["wa", "wb"] [.n 0] [], .dispatch (.n 1) ["ra", "rb"] [.n 0] [], .ret []]

/-- `useCd`'s certificate: each arm of the second dispatch sees the first's same arm's cell at the next
point serial (`0`). -/
def hUseCd : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[], [.ev 0, .ev 0]]
  rets := [[]]

theorem useCd_ok : heapOkC Data.powTree sigsC useCd hUseCd = true := by decide +kernel

/-- The arms swapped: arm `0` needs `p[1]`, which arm `0` of the first did not write. -/
theorem useCd_swap :
    heapOkC Data.powTree sigsC { useCd with body := [.dispatch (.n 1) ["wa", "wb"] [.n 0] [],
      .dispatch (.n 1) ["rb", "ra"] [.n 0] [], .ret []] } hUseCd = false := by
  decide +kernel

/-- Another selector: nothing under it. -/
theorem useCd_other :
    heapOkC Data.powTree sigsC { useCd with body := [.dispatch (.n 1) ["wa", "wb"] [.n 0] [],
      .dispatch (.n 2) ["ra", "rb"] [.n 0] [], .ret []] } hUseCd = false := by
  decide +kernel

/-! ## Merged residues -/

/-- `fill2` writes the two residues `p·g^(2j)`, `p·g^(2j+1)`, `j < e(n)`; `readAll2` needs `p·g^[0, e(n²))`. -/
def sigsM (g : String) : HSig :=
  if g = "fill2" then { postR := [⟨⟨[(0, 1)], 0⟩, 2, .num 0, .val 1⟩, ⟨⟨[(0, 1)], 1⟩, 2, .num 0, .val 1⟩] }
  else if g = "readAll2" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .mono ⟨[(1, 2)], 0⟩⟩] } else .empty

/-- Calls `fill2`, then `readAll2`. -/
def useM : Fn where
  name := "useM"
  params := [.n 0, .n 1]
  body := [.call "fill2" [.n 0, .n 1] [], .call "readAll2" [.n 0, .n 1] [], .ret []]

/-- `useM`'s certificate: `readAll2`'s run merged from `fill2`'s two residues (run serials `0`, `1`), the
root `n`'s exponent by the residual `0 < e(n)`. -/
def hUseM : HCert where
  sig := {}
  reads := []
  res := [.lt (.num 0) (.val 1)]
  calls := [[], [.mrg 2 [0], .run 0 [], .run 1 []]]
  rets := [[]]

theorem useM_ok : heapOkC Data.powTree sigsM useM hUseM = true := by decide +kernel

/-- Without a fact giving `n` an exponent, no merge. -/
theorem useM_noexp :
    heapOkC Data.powTree sigsM useM { hUseM with calls := [[], [.mrg 2 [], .run 0 [], .run 1 []]] } = false := by
  decide +kernel

/-- The residues in the wrong order. -/
theorem useM_bad :
    heapOkC Data.powTree sigsM useM { hUseM with calls := [[], [.mrg 2 [0], .run 1 [], .run 0 []]] } = false := by
  decide +kernel

/-! ## Words at return -/

/-- Stores `p·g` at `p[0]`. -/
def mkv : Fn where
  name := "mkv"
  params := [.n 0]
  body := [.atom (.const (.n 1) (word 2 0)), .atom (.mul (.n 2) (.n 0) (.n 1)), .atom (.load (.n 2) (.n 0) 0),
    .ret []]

/-- `mkv`'s certificate: `p[0]` written, holding `p·g` (`postV`, by the store, event `0`). -/
def hMkv : HCert where
  sig := { post := [⟨[(0, 1)], 0⟩], postV := [(0, ⟨[(0, 1)], 1⟩)] }
  reads := []
  res := []
  rets := [[.ev 0]]

theorem mkv_ok : heapOkC Data.powTree (fun _ ↦ .empty) mkv hMkv = true := by decide +kernel

/-- The word stored is not `p·g^2`. -/
theorem mkv_bad :
    heapOkC Data.powTree (fun _ ↦ .empty) mkv { hMkv with sig := { hMkv.sig with postV := [(0, ⟨[(0, 1)], 2⟩)] } } =
      false := by
  decide +kernel

/-- Calls `mkv`, reads `p[0]`, reads through the word read. -/
def useV : Fn where
  name := "useV"
  params := [.n 0]
  body := [.call "mkv" [.n 0] [], .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 0), .ret []]

/-- `useV`'s certificate: the read of `p[0]` is the call's `post` cell (serial `0`), whose word `mkv`
names (`hvs`): `p·g`, the precondition the second read is. -/
def hUseV : HCert where
  sig := { pre := [⟨[(0, 1)], 1⟩] }
  reads := [(1, [(0, 0, .ev 0)]), (2, [(1, 0, .pre 0)])]
  res := []
  calls := [[]]
  rets := [[]]
  hvs := [1]

theorem useV_ok : heapOkC Data.powTree (fun g ↦ if g = "mkv" then hMkv.sig else .empty) useV hUseV = true := by
  decide +kernel

/-- Without `mkv`'s `postV`, the word read is its own base. -/
theorem useV_bad :
    heapOkC Data.powTree (fun g ↦ if g = "mkv" then { post := [⟨[(0, 1)], 0⟩] } else .empty) useV hUseV = false := by
  decide +kernel

/-! ## Branch paths (round 4) -/

/-- Reads `p[1]` in arm `2` of a `match` on `x`. -/
def armRd : Fn where
  name := "armRd"
  params := [.n 0, .n 1]
  body := [.match_ (.n 1) [[], [], [.atom (.load (.n 2) (.n 0) 1)]], .ret []]

/-- `armRd`'s certificate: the precondition run `p·g^[0, e(x))`, the read inside it by the arm's own
fact `e(x) = 2` (no residual). -/
def hArmRd : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] }
  reads := [(2, [(0, 1, .run 0 [])])]
  res := []
  rets := [[]]

theorem armRd_ok : heapOkC Data.powTree (fun _ ↦ .empty) armRd hArmRd = true := by decide +kernel

/-- `p[2]` in arm `2`: past the run. -/
theorem armRd_past :
    heapOkC Data.powTree (fun _ ↦ .empty) { armRd with body := [.match_ (.n 1) [[], [], [.atom (.load (.n 2) (.n 0) 2)]],
      .ret []] } { hArmRd with reads := [(2, [(0, 2, .run 0 [])])] } = false := by
  decide +kernel

/-- `p[1]` in arm `1`: past the run there. -/
theorem armRd_arm1 :
    heapOkC Data.powTree (fun _ ↦ .empty) { armRd with body := [.match_ (.n 1) [[], [.atom (.load (.n 2) (.n 0) 1)], []],
      .ret []] } hArmRd = false := by
  decide +kernel

/-- Reads `p[5]` where `c = 0`. -/
def ifRd : Fn where
  name := "ifRd"
  params := [.n 0, .n 1, .n 2]
  body := [.ite (.n 1) [.atom (.load (.n 3) (.n 0) 5)] [], .ret []]

/-- `ifRd`'s certificate: the precondition run `p·g^[0, e(n))`, the read by the residual `5 < e(n)`
asked where `c = 0` only. -/
def hIfRd : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := [(3, [(0, 5, .run 0 [0])])]
  res := [.under [.zero 1] (.lt (.num 5) (.val 2))]
  rets := [[]]

theorem ifRd_ok : heapOkC Data.powTree (fun _ ↦ .empty) ifRd hIfRd = true := by decide +kernel

/-- The read on the other side, where the residual is not asked. -/
theorem ifRd_bad :
    heapOkC Data.powTree (fun _ ↦ .empty) { ifRd with body := [.ite (.n 1) [] [.atom (.load (.n 3) (.n 0) 5)], .ret []] }
      hIfRd = false := by
  decide +kernel

/-- `fillN p n` guarantees `p·g^[0, e(n))`. -/
def sigsZ (g : String) : HSig :=
  if g = "fillN" then { postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] } else .empty

/-- Guarantees `p·g^[0, e(n))`: `fillN p n` unless `n = 1`, where the run is empty. -/
def zDup : Fn where
  name := "zDup"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 1 0)), .atom (.add (.n 3) (.n 1) (.n 2)),
    .ite (.n 3) [] [.call "fillN" [.n 0, .n 1] []], .ret []]

/-- `zDup`'s certificate: the `ret` checked in each branch, empty where `n + 1 = 0`, `fillN`'s run otherwise. -/
def hZDup : HCert where
  sig := { postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] }
  reads := []
  res := []
  calls := [[]]
  rets := [[.empty], [.run 0 []]]
  dups := [3]

theorem zDup_ok : heapOkC Data.powTree sigsZ zDup hZDup = true := by decide +kernel

/-- Without `dups`, one `ret` after the join: neither branch's witness holds there. -/
theorem zDup_nodup : heapOkC Data.powTree sigsZ zDup { hZDup with dups := [], rets := [[.empty]] } = false := by
  decide +kernel

theorem zDup_nodup2 : heapOkC Data.powTree sigsZ zDup { hZDup with dups := [], rets := [[.run 0 []]] } = false := by
  decide +kernel

/-- The call in the zero branch: the other branch's run is not empty (no equation there). -/
theorem zDup_bad : heapOkC Data.powTree sigsZ
    { zDup with body := [.atom (.const (.n 2) (word 1 0)), .atom (.add (.n 3) (.n 1) (.n 2)),
      .ite (.n 3) [.call "fillN" [.n 0, .n 1] []] [], .ret []] } { hZDup with rets := [[.run 0 []], [.empty]] } = false := by
  decide +kernel

/-- The guard's sum not over the bounds: `n + p = 0` makes no run of `p·g^[0, e(n))` empty. -/
theorem zDup_bad2 : heapOkC Data.powTree sigsZ
    { zDup with body := [.atom (.add (.n 3) (.n 1) (.n 0)), .ite (.n 3) [] [.call "fillN" [.n 0, .n 1] []], .ret []] }
    hZDup = false := by
  decide +kernel

/-- Reads `p·i`, `e(i) ≤ e(n)`: the run `p·g^[0, e(n))` and its next point `p·n`. -/
def appRd : Fn where
  name := "appRd"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.mul (.n 3) (.n 0) (.n 2)), .atom (.load (.n 4) (.n 3) 0), .ret []]

/-- `appRd`'s certificate: the read by `app`, the point `p·n` a precondition, the residual `e(i) < e(n·g)`. -/
def hAppRd : HCert where
  sig := { pre := [⟨[(0, 1), (1, 1)], 0⟩], preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] }
  reads := [(4, [(3, 0, .app 0 (.pre 0) [0])])]
  res := [.lt (.val 2) (.mono ⟨[(1, 1)], 1⟩)]
  rets := [[]]

theorem appRd_ok : heapOkC Data.powTree (fun _ ↦ .empty) appRd hAppRd = true := by decide +kernel

/-- Without the next point. -/
theorem appRd_nopt : heapOkC Data.powTree (fun _ ↦ .empty) appRd
    { hAppRd with sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] } } = false := by
  decide +kernel

/-- The index up to two past the run: `p·n·g` is not written. -/
theorem appRd_far : heapOkC Data.powTree (fun _ ↦ .empty) appRd
    { hAppRd with res := [.lt (.val 2) (.mono ⟨[(1, 1)], 2⟩)] } = false := by
  decide +kernel

/-- Guarantees `p·g^[0, e(m))` from the residues `p·g^r·g^(2·[0, e(n)))`, `e(m) ≤ 2·e(n)` by a fact. -/
def mrgLe : Fn where
  name := "mrgLe"
  params := [.n 0, .n 1, .n 2]
  body := [.ret []]

def hMrgLe : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 2, .num 0, .val 1⟩, ⟨⟨[(0, 1)], 1⟩, 2, .num 0, .val 1⟩],
           postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := []
  res := [.lt (.val 2) (.mono ⟨[(1, 2)], 1⟩), .lt (.val 1) (.num 100)]
  rets := [[.mrgE 2 ⟨[(1, 1)], 0⟩ [0, 1], .run 0 [], .run 1 []]]

theorem mrgLe_ok : heapOkC Data.powTree (fun _ ↦ .empty) mrgLe hMrgLe = true := by decide +kernel

/-- `e(m) ≤ 2·e(n) + 1` is not enough. -/
theorem mrgLe_bad : heapOkC Data.powTree (fun _ ↦ .empty) mrgLe
    { hMrgLe with res := [.lt (.val 2) (.mono ⟨[(1, 2)], 2⟩), .lt (.val 1) (.num 100)] } = false := by
  decide +kernel

/-- `fillE p n` guarantees the cell `p·n` (as a run of one cell). -/
def sigsFE (g : String) : HSig :=
  if g = "fillE" then { postR := [⟨⟨[(0, 1), (1, 1)], 0⟩, 1, .num 0, .num 1⟩] } else .empty

/-- Stores at `p`, then `fillE p n` unless `n = 1`: the cell `p·n` is written either way. -/
def keepF : Fn where
  name := "keepF"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 0) 0), .atom (.const (.n 3) (word 1 0)),
    .atom (.add (.n 4) (.n 3) (.n 1)), .callIf (.n 4) "fillE" [.n 0, .n 1], .ret []]

/-- `keepF`'s certificate: `fillE`'s run kept, where it is not entered `p·g^[0, 1)` by the store. -/
def hKeepF : HCert where
  sig := { postR := [⟨⟨[(0, 1), (1, 1)], 0⟩, 1, .num 0, .num 1⟩] }
  reads := []
  res := []
  calls := [[.keep 0 ⟨[(0, 1)], 0⟩ ⟨[], 0⟩ ⟨[], 1⟩, .pts, .ev 0]]
  rets := [[.run 0 []]]

theorem keepF_ok : heapOkC Data.powTree sigsFE keepF hKeepF = true := by decide +kernel

/-- Not kept: nothing in scope at the `ret`. -/
theorem keepF_nokeep : heapOkC Data.powTree sigsFE keepF { hKeepF with calls := [[]] } = false := by decide +kernel

/-- Kept as another run: `p·g` is not `p·n` where `n = 1`. -/
theorem keepF_bad : heapOkC Data.powTree sigsFE keepF
    { hKeepF with calls := [[.keep 0 ⟨[(0, 1)], 1⟩ ⟨[], 0⟩ ⟨[], 1⟩, .pts, .ev 0]] } = false := by
  decide +kernel

/-- Hints 2048 cells at `p` (a stream) and guarantees them as one run (`hintRun`). -/
def hintR : Fn where
  name := "hintR"
  params := [.n 0]
  body := [.atom (.hint (.witness "stream" (.heap (.n 0) 0 2048))), .ret []]

def hHintR : HCert where
  sig := { postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 2048⟩] }
  reads := []
  res := []
  rets := [[.run 0 []]]

theorem hintR_ok : heapOkC Data.powTree (fun _ ↦ .empty) hintR hHintR = true := by decide +kernel

/-- One cell more than written. -/
theorem hintR_bad : heapOkC Data.powTree (fun _ ↦ .empty) hintR
    { hHintR with sig := { postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 2049⟩] } } = false := by
  decide +kernel

/-- `rd3` needs `p·g^[0, 3)`. -/
def sigsB (g : String) : HSig :=
  if g = "rd3" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 3⟩] } else .empty

/-- Dispatches on `x` to `rd3` in arm `1`, and calls `rd3` if `c ≠ 0`. -/
def armCall : Fn where
  name := "armCall"
  params := [.n 0, .n 1, .n 2]
  body := [.dispatch (.n 1) ["none", "rd3"] [.n 0] [], .callIf (.n 1) "rd3" [.n 0], .ret []]

/-- `armCall`'s certificate: `rd3`'s precondition inside the own run `p·g^[0, e(n))` by `2 < e(n)`, a
residual asked in arm `1` (for the dispatch) and where `x ≠ 0` (for the `callIf`). -/
def hArmCall : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := []
  res := [.under [.arm 1 1] (.lt (.num 2) (.val 2)), .under [.nonzero 1] (.lt (.num 2) (.val 2))]
  calls := [[.run 0 [0]], [.run 0 [1]]]
  rets := [[]]

theorem armCall_ok : heapOkC Data.powTree sigsB armCall hArmCall = true := by decide +kernel

/-- The dispatch's residual asked in arm `0`: not in arm `1`. -/
theorem armCall_bad :
    heapOkC Data.powTree sigsB armCall
      { hArmCall with res := [.under [.arm 1 0] (.lt (.num 2) (.val 2)), .under [.nonzero 1] (.lt (.num 2) (.val 2))] } =
      false := by
  decide +kernel

/-- The `callIf`'s residual asked where `x = 0`. -/
theorem armCall_bad2 :
    heapOkC Data.powTree sigsB armCall
      { hArmCall with res := [.under [.arm 1 1] (.lt (.num 2) (.val 2)), .under [.zero 1] (.lt (.num 2) (.val 2))] } =
      false := by
  decide +kernel

/-! ## A cell among cells, a run's point before it, a dispatch's returned pointers (round 4) -/

/-- Stores at `p·a` and `p·b` (hinted indices), reads `p[0]`. -/
def pm : Fn where
  name := "pm"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.const (.n 3) (word 0 0)), .atom (.mul (.n 4) (.n 0) (.n 1)), .atom (.load (.n 3) (.n 4) 0),
    .atom (.mul (.n 5) (.n 0) (.n 2)), .atom (.load (.n 3) (.n 5) 0), .atom (.load (.n 6) (.n 0) 0), .ret []]

/-- `pm`'s certificate: `p[0]` is one of `p·a`, `p·b` (`subP`), the stores `0`, `1`. -/
def hPm : HCert where
  sig := {}
  reads := [(6, [(0, 0, .perm 0 [0, 1])])]
  res := [.subP ⟨[(0, 1)], 0⟩ [⟨[(0, 1), (1, 1)], 0⟩, ⟨[(0, 1), (2, 1)], 0⟩]]
  rets := [[]]

theorem pm_ok : heapOkC Data.powTree (fun _ ↦ .empty) pm hPm = true := by decide +kernel

/-- The serials swapped. -/
theorem pm_swap : heapOkC Data.powTree (fun _ ↦ .empty) pm { hPm with reads := [(6, [(0, 0, .perm 0 [1, 0])])] } =
    false := by
  decide +kernel

/-- A residual about another cell. -/
theorem pm_other :
    heapOkC Data.powTree (fun _ ↦ .empty) pm
      { hPm with res := [.subP ⟨[(0, 1)], 1⟩ [⟨[(0, 1), (1, 1)], 0⟩, ⟨[(0, 1), (2, 1)], 0⟩]] } = false := by
  decide +kernel

/-- `fillR` writes `p·g^(1+j)`, `j < e(n)`. -/
def sigsR (g : String) : HSig :=
  if g = "fillR" then { postR := [⟨⟨[(0, 1)], 1⟩, 1, .num 0, .val 1⟩] } else .empty

/-- Stores `p[0]`, calls `fillR`, reads `p·n` (row `n` of a table whose row `0` is the point). -/
def prp : Fn where
  name := "prp"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 0) 0), .call "fillR" [.n 0, .n 1] [],
    .atom (.mul (.n 3) (.n 0) (.n 1)), .atom (.load (.n 4) (.n 3) 0), .ret []]

/-- `prp`'s certificate: the read in `fillR`'s run extended by the store before it (`prep`), `e(n)` by the
residual `0 < e(n)`. -/
def hPrp : HCert where
  sig := {}
  reads := [(4, [(3, 0, .prep 0 (.ev 0) [0])])]
  res := [.lt (.num 0) (.val 1)]
  calls := [[]]
  rets := [[]]

theorem prp_ok : heapOkC Data.powTree sigsR prp hPrp = true := by decide +kernel

/-- No exponent for the upper bound. -/
theorem prp_noexp : heapOkC Data.powTree sigsR prp { hPrp with reads := [(4, [(3, 0, .prep 0 (.ev 0) [])])] } =
    false := by
  decide +kernel

/-- The read one past: `p·n·g`. -/
theorem prp_past :
    heapOkC Data.powTree sigsR { prp with body := [.atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 0) 0),
      .call "fillR" [.n 0, .n 1] [], .atom (.mul (.n 3) (.n 0) (.n 1)), .atom (.load (.n 4) (.n 3) 1), .ret []] }
      { hPrp with reads := [(4, [(3, 1, .prep 0 (.ev 0) [0])])] } = false := by
  decide +kernel

/-- `ra` returns `p`, `rb` returns `p·g^2`. -/
def sigsV (g : String) : HSig :=
  if g = "ra" then { retM := [(0, ⟨[(0, 1)], 0⟩)] }
  else if g = "rb" then { retM := [(0, ⟨[(0, 1)], 2⟩)] } else .empty

/-- Stores `p[0..3]`, dispatches on `x` to `ra`, `rb`, reads `r[0]`, `r[1]`, returns `r`. -/
def vpd : Fn where
  name := "vpd"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 1) 0), .atom (.load (.n 2) (.n 1) 1),
    .atom (.load (.n 2) (.n 1) 2), .atom (.load (.n 2) (.n 1) 3), .dispatch (.n 0) ["ra", "rb"] [.n 1] [.n 3],
    .atom (.load (.n 4) (.n 3) 0), .atom (.load (.n 5) (.n 3) 1), .ret [.n 3]]

/-- `vpd`'s certificate: the returned word `r` with its cells `0`, `1` written whichever arm ran (`vp`:
arm `ra`'s `p[0]`, `p[1]`, arm `rb`'s `p[2]`, `p[3]`), pushed at serials `4`, `5`, read and guaranteed
over the returned slot. -/
def hVpd : HCert where
  sig := { post := [⟨[(2, 1)], 0⟩, ⟨[(2, 1)], 1⟩] }
  reads := [(4, [(3, 0, .ev 4)]), (5, [(3, 1, .ev 5)])]
  res := []
  calls := [[.vp 0 [0, 1], .ev 0, .ev 1, .ev 2, .ev 3]]
  rets := [[.ev 4, .ev 5]]

theorem vpd_ok : heapOkC Data.powTree sigsV vpd hVpd = true := by decide +kernel

/-- Three cells: arm `rb`'s `p[4]` is not written. -/
theorem vpd_bad :
    heapOkC Data.powTree sigsV vpd { hVpd with calls := [[.vp 0 [0, 1, 2], .ev 0, .ev 1, .ev 2, .ev 2, .ev 3, .ev 3]] } =
      false := by
  decide +kernel

/-- Arm `rb` witnessed by `ra`'s cells. -/
theorem vpd_bad2 :
    heapOkC Data.powTree sigsV vpd { hVpd with calls := [[.vp 0 [0, 1], .ev 0, .ev 1, .ev 0, .ev 1]] } = false := by
  decide +kernel

/-! ## Equations at return, a bound renamed (round 4) -/

/-- `gap = g^32 / n`: no monomial for the quotient; returns it. -/
def dvd : Fn where
  name := "dvd"
  params := [.n 0]
  body := [.atom (.const (.n 1) (word 4294967296 0)), .atom (.mul (.n 1) (.n 2) (.n 0)), .ret [.n 2]]

/-- `dvd`'s certificate: the `mul`'s equation kept (`eqs`), `gap·n = g^32` at return (`retEq`). -/
def hDvd : HCert where
  sig := { retEq := [(⟨[(0, 1), (1, 1)], 0⟩, ⟨[], 32⟩)] }
  reads := []
  res := []
  rets := [[]]
  eqs := [1]

theorem dvd_ok : heapOkC Data.powTree (fun _ ↦ .empty) dvd hDvd = true := by decide +kernel

/-- Without the equation kept. -/
theorem dvd_bad : heapOkC Data.powTree (fun _ ↦ .empty) dvd { hDvd with eqs := [] } = false := by decide +kernel

/-- `fillG` writes `r·g^j`, `j < e((gap·n)^2)`; `need64` needs `r·g^[0, 64)`. -/
def sigsE (g : String) : HSig :=
  if g = "dvd" then hDvd.sig
  else if g = "fillG" then { postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .mono ⟨[(1, 2), (2, 2)], 0⟩⟩] }
  else if g = "need64" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 64⟩] }
  else if g = "need65" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 65⟩] } else .empty

/-- Calls `dvd`, `fillG`, `need64`. -/
def useDv : Fn where
  name := "useDv"
  params := [.n 0, .n 1]
  body := [.call "dvd" [.n 1] [.n 2], .call "fillG" [.n 0, .n 2, .n 1] [], .call "need64" [.n 0] [], .ret []]

/-- `useDv`'s certificate: `need64`'s run is `fillG`'s, its bound `(gap·n)^2` renamed to `g^64` by `dvd`'s
equation. -/
def hUseDv : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[], [], [.run 0 []]]
  rets := [[]]

theorem useDv_ok : heapOkC Data.powTree sigsE useDv hUseDv = true := by decide +kernel

/-- `g^65` is not `(gap·n)^2`. -/
theorem useDv_bad :
    heapOkC Data.powTree sigsE { useDv with body := [.call "dvd" [.n 1] [.n 2], .call "fillG" [.n 0, .n 2, .n 1] [],
      .call "need65" [.n 0] [], .ret []] } hUseDv = false := by
  decide +kernel

/-! ## A long point run (round 4) -/

/-- `big` guarantees the `2048` points `p·g^i`; `need2k` needs the run `p·g^[0, 2048)`. -/
def sigsL (g : String) : HSig :=
  if g = "big" then { post := (List.range 2048).map fun i ↦ ⟨[(0, 1)], i⟩ }
  else if g = "need2k" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 2048⟩] } else .empty

/-- Calls `big`, then `need2k`. -/
def useBig : Fn where
  name := "useBig"
  params := [.n 0]
  body := [.call "big" [.n 0] [], .call "need2k" [.n 0] [], .ret []]

/-- `useBig`'s certificate: the run met by its `2048` points (`pts`). -/
def hUseBig : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[], .pts :: (List.range 2048).map .ev]
  rets := [[]]

theorem useBig_ok : heapOkC Data.powTree sigsL useBig hUseBig = true := by decide +kernel

/-- One point short. -/
theorem useBig_bad :
    heapOkC Data.powTree sigsL useBig { hUseBig with calls := [[], .pts :: (List.range 2047).map .ev] } = false := by
  decide +kernel

/-! ## A selector's base under an arm (round 4) -/

/-- Matches on `x = b·g^2`; arm `3` reads `p[0]`. -/
def selB : Fn where
  name := "selB"
  params := [.n 0, .n 1]
  body := [.atom (.const (.n 2) (word 4 0)), .atom (.mul (.n 3) (.n 1) (.n 2)),
    .match_ (.n 3) [[], [], [], [.atom (.load (.n 4) (.n 0) 0)]], .ret []]

/-- `selB`'s certificate: the precondition run `p·g^[0, e(b))`, `e(b) = 1` in arm `3` (`b = x·g^-2`). -/
def hSelB : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] }
  reads := [(4, [(0, 0, .run 0 [])])]
  res := []
  rets := [[]]

theorem selB_ok : heapOkC Data.powTree (fun _ ↦ .empty) selB hSelB = true := by decide +kernel

/-- `p[1]` in arm `3`: past `e(b) = 1`. -/
theorem selB_bad :
    heapOkC Data.powTree (fun _ ↦ .empty) { selB with body := [.atom (.const (.n 2) (word 4 0)),
      .atom (.mul (.n 3) (.n 1) (.n 2)), .match_ (.n 3) [[], [], [], [.atom (.load (.n 4) (.n 0) 1)]], .ret []] }
      { hSelB with reads := [(4, [(0, 1, .run 0 [])])] } = false := by
  decide +kernel

/-! ## Requests from emit: the cell before the upper bound, a bound past a fact, `log2Ceil` bits, a dispatch's
words at return (round 4) -/

/-- `recs` writes the records `p·g^(5 + 4j)`, `j < e(h)`; `needR` needs `p·g^[0, e(n·g))`. -/
def sigsQ (g : String) : HSig :=
  if g = "recs" then { postR := [⟨⟨[(0, 1)], 5⟩, 4, .num 0, .val 1⟩] }
  else if g = "needR" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .mono ⟨[(1, 1)], 1⟩⟩] } else .empty

/-- Calls `recs`, reads `p·h^4·g`, the last record's cell. -/
def lastRec : Fn where
  name := "lastRec"
  params := [.n 0, .n 1]
  body := [.call "recs" [.n 0, .n 1] [], .atom (.mul (.n 2) (.n 1) (.n 1)), .atom (.mul (.n 3) (.n 2) (.n 2)),
    .atom (.mul (.n 4) (.n 0) (.n 3)), .atom (.load (.n 5) (.n 4) 1), .ret []]

/-- `lastRec`'s certificate: the cell one index below `h` (`ptBack`), `e(h) ≥ 1` by a residual. -/
def hLastRec : HCert where
  sig := {}
  reads := [(5, [(4, 1, .run 0 [0])])]
  res := [.lt (.num 0) (.val 1)]
  calls := [[]]
  rets := [[]]

theorem lastRec_ok : heapOkC Data.powTree sigsQ lastRec hLastRec = true := by decide +kernel

/-- Without `e(h) ≥ 1`. -/
theorem lastRec_bad : heapOkC Data.powTree sigsQ lastRec { hLastRec with reads := [(5, [(4, 1, .run 0 [])])] } =
    false := by
  decide +kernel

/-- Calls `needR` on `p`, `n`, its own run `p·g^[0, e(m))`. -/
def hiF : Fn where
  name := "hiF"
  params := [.n 0, .n 1, .n 2]
  body := [.call "needR" [.n 0, .n 1] [], .ret []]

/-- `hiF`'s certificate: `e(n·g) ≤ e(m)` by the residual `e(n) < e(m)`. -/
def hHiF : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := []
  res := [.lt (.val 1) (.val 2)]
  calls := [[.run 0 [0]]]
  rets := [[]]

theorem hiF_ok : heapOkC Data.powTree sigsQ hiF hHiF = true := by decide +kernel

theorem hiF_bad : heapOkC Data.powTree sigsQ hiF { hHiF with calls := [[.run 0 []]] } = false := by decide +kernel

/-- `log2Ceil` of the 4 bits at `p[0..3]`. -/
def lg : Fn where
  name := "lg"
  params := [.n 0]
  body := [.atom (.hint (.log2Ceil (.heap (.n 0) 0 4) 4 0 (.n 1))), .ret []]

/-- `lg`'s certificate: the bits are preconditions, keyed as reads of the destination. -/
def hLg : HCert where
  sig := { pre := [⟨[(0, 1)], 0⟩, ⟨[(0, 1)], 1⟩, ⟨[(0, 1)], 2⟩, ⟨[(0, 1)], 3⟩] }
  reads := [(1, [(0, 0, .pre 0), (0, 1, .pre 1), (0, 2, .pre 2), (0, 3, .pre 3)])]
  res := []
  rets := [[]]

theorem lg_ok : heapOkC Data.powTree (fun _ ↦ .empty) lg hLg = true := by decide +kernel

/-- A bit without its witness. -/
theorem lg_bad :
    heapOkC Data.powTree (fun _ ↦ .empty) lg { hLg with reads := [(1, [(0, 0, .pre 0), (0, 1, .pre 1), (0, 2, .pre 2)])] } =
      false := by
  decide +kernel

/-- `wa`, `wb` both store `p·g` at `p[0]`; `wc` stores `p·g^2`. -/
def sigsDV (g : String) : HSig :=
  if g = "wa" ∨ g = "wb" then { post := [⟨[(0, 1)], 0⟩], postV := [(0, ⟨[(0, 1)], 1⟩)] }
  else if g = "wc" then { post := [⟨[(0, 1)], 0⟩], postV := [(0, ⟨[(0, 1)], 2⟩)] } else .empty

/-- Dispatches on `x` to `wa`, `wb`, reads `p[0]` and through it. -/
def useDV : Fn where
  name := "useDV"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 0) ["wa", "wb"] [.n 1] [], .atom (.load (.n 2) (.n 1) 0), .atom (.load (.n 3) (.n 2) 0),
    .ret []]

/-- `useDV`'s certificate: the meet's cell (serial `0`) holds `p·g` (every arm's `postV`), read back
(`hvs`), the precondition `p·g` read through it. -/
def hUseDV : HCert where
  sig := { pre := [⟨[(1, 1)], 1⟩] }
  reads := [(2, [(1, 0, .ev 0)]), (3, [(2, 0, .pre 0)])]
  res := []
  calls := [[]]
  rets := [[]]
  hvs := [2]

theorem useDV_ok : heapOkC Data.powTree sigsDV useDV hUseDV = true := by decide +kernel

/-- An arm naming another word. -/
theorem useDV_bad :
    heapOkC Data.powTree sigsDV { useDV with body := [.dispatch (.n 0) ["wa", "wc"] [.n 1] [],
      .atom (.load (.n 2) (.n 1) 0), .atom (.load (.n 3) (.n 2) 0), .ret []] } hUseDV = false := by
  decide +kernel

/-- A frame run `p = [v₂, v₃, v₄]` (`frameAddr`), `v₂` by a hint and `v₃` by a constant after it, `v₄` never
defined; `p` stored at `p₀[0]` (as `decode_query_windows`). -/
def fa1 : Fn where
  name := "fa1"
  params := [.n 0]
  body := [.atom (.frameAddr (.n 1) [.n 2, .n 3, .n 4]), .atom (.hint (.witness "s" (.stack [.n 2]))),
    .atom (.const (.n 3) (word 0 0)), .atom (.load (.n 1) (.n 0) 0), .ret []]

/-- `fa1`'s certificate: the word at `p₀[0]` points to two written cells, the frame run's cells `0` and `1`
(`fas`), pushed at the return after the store's event (serials `1`, `2`). -/
def hFa1 : HCert where
  sig := { post := [⟨[(0, 1)], 0⟩], postP := [(⟨[(0, 1)], 0⟩, [0, 1])] }
  reads := []
  res := []
  rets := [[.ev 0, .word 0, .ev 1, .ev 2]]
  fas := [(1, 0), (1, 1)]

theorem fa1_ok : heapOkC Data.powTree (fun _ ↦ .empty) fa1 hFa1 = true := by decide +kernel

/-- The caller reads through the stored pointer (`usep`'s pattern). -/
def useFa1 : Fn where
  name := "useFa1"
  params := [.n 0]
  body := [.call "fa1" [.n 0] [], .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 1), .ret []]

def hUseFa1 : HCert where
  sig := {}
  reads := [(1, [(0, 0, .ev 0)]), (2, [(1, 1, .pf 1)])]
  res := []
  calls := [[]]
  rets := [[]]

theorem useFa1_ok : heapOkC Data.powTree (fun g ↦ if g = "fa1" then hFa1.sig else .empty) useFa1 hUseFa1 = true := by
  decide +kernel

/-- Cell `2` of the run: its value `v₄` is defined by no atom. -/
theorem fa1_bad_undef :
    heapOkC Data.powTree (fun _ ↦ .empty) fa1
      { hFa1 with sig := { post := [⟨[(0, 1)], 0⟩], postP := [(⟨[(0, 1)], 0⟩, [0, 2])] }, fas := [(1, 0), (1, 2)] } =
      false := by
  decide +kernel

/-- No `fas`: the run's cells are not written. -/
theorem fa1_bad_none : heapOkC Data.powTree (fun _ ↦ .empty) fa1 { hFa1 with fas := [] } = false := by decide +kernel

/-- A `fas` naming a value that is no `frameAddr`'s pointer. -/
theorem fa1_bad_ptr :
    heapOkC Data.powTree (fun _ ↦ .empty) fa1 { hFa1 with fas := [(0, 0), (1, 1)] } = false := by
  decide +kernel

/-- The `frameAddr` under a branch: not on every path that returns. -/
theorem fa1_bad_branch :
    heapOkC Data.powTree (fun _ ↦ .empty)
      { fa1 with body := [.ite (.n 0) [.atom (.frameAddr (.n 1) [.n 2, .n 3, .n 4])] [],
        .atom (.hint (.witness "s" (.stack [.n 2]))), .atom (.const (.n 3) (word 0 0)), .atom (.load (.n 1) (.n 0) 0),
        .ret []] } hFa1 = false := by
  decide +kernel

/-- The defining atoms past a statement with a `ret`: not on every path that returns. -/
theorem fa1_bad_ret :
    heapOkC Data.powTree (fun _ ↦ .empty)
      { fa1 with body := [.atom (.frameAddr (.n 1) [.n 2, .n 3, .n 4]), .ite (.n 0) [.ret []] [],
        .atom (.hint (.witness "s" (.stack [.n 2]))), .atom (.const (.n 3) (word 0 0)), .atom (.load (.n 1) (.n 0) 0),
        .ret []] } { hFa1 with rets := [[], [.ev 0, .word 0, .ev 1, .ev 2]] } = false := by
  decide +kernel

/-- A frame run over values defined before it, its pointer moved by `g` and returned (as `da_expand`): the
returned word's cell `0` is the run's cell `1`. -/
def fa2 : Fn where
  name := "fa2"
  params := [.n 0]
  body := [.atom (.mul (.n 1) (.n 0) (.n 0)), .atom (.add (.n 2) (.n 0) (.n 0)),
    .atom (.frameAddr (.n 3) [.n 1, .n 2]), .atom (.const (.n 4) (word 2 0)), .atom (.mul (.n 5) (.n 3) (.n 4)),
    .ret [.n 5]]

/-- `fa2`'s certificate: `post` over the returned word (slot `1`), `p₃·g` in the pass, the run's cell `1`. -/
def hFa2 : HCert where
  sig := { post := [⟨[(1, 1)], 0⟩] }
  reads := []
  res := []
  rets := [[.ev 0]]
  fas := [(3, 1)]

theorem fa2_ok : heapOkC Data.powTree (fun _ ↦ .empty) fa2 hFa2 = true := by decide +kernel

/-- The run's cell `0` is not the returned word's cell `0`. -/
theorem fa2_bad : heapOkC Data.powTree (fun _ ↦ .empty) fa2 { hFa2 with fas := [(3, 0)] } = false := by decide +kernel

/-! ## Words at cells (round 6, E11) -/

/-- Loads the pointer `x` stored at `q[0]`, reads `x[0]`, `x[1]`. -/
def rdd : Fn where
  name := "rdd"
  params := [.n 0]
  body := [.atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 0), .atom (.load (.n 3) (.n 1) 1), .ret []]

/-- `rdd`'s certificate: `q[0]` written (`pre`); one ghost (slot `1`, value `GB`), the object `q[0]` points to,
its cells `G·g^[0, 2)` a precondition; the reads in it by the residual "`x·g^[0, 2)` is in the object". -/
def hRdd : HCert where
  sig := { pre := [⟨[(0, 1)], 0⟩], preR := [⟨⟨[(1, 1)], 0⟩, 1, .num 0, .num 2⟩], ghosts := 1 }
  reads := [(1, [(0, 0, .pre 0)]), (2, [(1, 0, .run 0 [0])]), (3, [(1, 1, .run 0 [0])])]
  res := [.subR ⟨⟨[(1, 1)], 0⟩, 1, .num 0, .num 2⟩ ⟨⟨[(1048576, 1)], 0⟩, 1, .num 0, .num 2⟩]
  rets := [[]]

theorem rdd_ok : heapOkC Data.powTree (fun _ ↦ .empty) rdd hRdd = true := by decide +kernel

/-- A body naming a word at a cell's value (`DB`) is refused. -/
theorem rdd_named :
    heapOkC Data.powTree (fun _ ↦ .empty) { rdd with body := [.atom (.load (.n 1) (.n 0) 0),
      .atom (.load (.n 524288) (.n 1) 0), .atom (.load (.n 3) (.n 1) 1), .ret []] } hRdd = false := by
  decide +kernel

/-- `mkp` and `rdd`. -/
def sigsD (g : String) : HSig := if g = "mkp" then hMkp.sig else if g = "rdd" then hRdd.sig else .empty

/-- Calls `mkp` (it stores at `p[0]` a pointer to two written cells), then `rdd` on `p`, never loading `p[0]`. -/
def useD : Fn where
  name := "useD"
  params := [.n 0]
  body := [.call "mkp" [.n 0] [], .call "rdd" [.n 0] [], .ret []]

/-- `useD`'s certificate: `rdd`'s ghost is the word at `p[0]` (`ders`, the value `DB`): the cell witnessed first
(`mkp`'s `post`, point serial `0`), then `rdd`'s `pre` (the same cell) and its object's two cells, each past the
word at `p[0]` by `mkp`'s pointer fact (serial `1`), `DB` loaded from `p[0]`. -/
def hUseD : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[], [.ev 0, .ev 0, .pts, .pf 1, .pf 1]]
  rets := [[]]
  gargs := [("rdd", [0], [⟨[(524288, 1)], 0⟩])]
  ders := [⟨[(0, 1)], 0⟩]

theorem useD_ok : heapOkC Data.powTree sigsD useD hUseD = true := by decide +kernel

/-- The cell of the word at a cell not witnessed. -/
theorem useD_nowit : heapOkC Data.powTree sigsD useD { hUseD with calls := [[], [.ev 0, .pts, .pf 1, .pf 1]] } = false := by
  decide +kernel

/-- No such word at a cell. -/
theorem useD_noders : heapOkC Data.powTree sigsD useD { hUseD with ders := [] } = false := by decide +kernel

/-- The ghost named by `p` itself: no pointer fact holds `p`'s cells. -/
theorem useD_self :
    heapOkC Data.powTree sigsD useD
      { hUseD with calls := [[], [.ev 0, .pts, .pf 1, .pf 1]], gargs := [("rdd", [0], [⟨[(0, 1)], 0⟩])] } = false := by
  decide +kernel

/-- A word at a cell over a word at a cell is refused. -/
theorem useD_nested :
    heapOkC Data.powTree sigsD useD { hUseD with ders := [⟨[(524288, 1)], 0⟩] } = false := by
  decide +kernel

/-! ## A run split at a symbolic index (round 6, E10) -/

/-- `need4` needs `p·g^[0, 4)`. -/
def sigsK (g : String) : HSig := if g = "need4" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 4⟩] } else .empty

/-- `a·b = g^4` (a `mul` whose product is known), then `need4` on `p`. -/
def catk : Fn where
  name := "catk"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.const (.n 3) (word 16 0)), .atom (.mul (.n 3) (.n 1) (.n 2)), .call "need4" [.n 0] [], .ret []]

/-- `catk`'s certificate: `p·g^[0, e(a))` and `p·a·g^[0, e(b))` preconditions, `need4`'s run split at `a`
(`catM a b`: `a·b = g^4` by the kept equation, the exponents by the residuals). -/
def hCatk : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩, ⟨⟨[(0, 1), (1, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := []
  res := [.lt (.num 0) (.val 1), .lt (.num 0) (.val 2)]
  calls := [[.catM ⟨[(1, 1)], 0⟩ ⟨[(2, 1)], 0⟩ [0, 1], .run 0 [], .run 1 []]]
  rets := [[]]
  eqs := [3]

theorem catk_ok : heapOkC Data.powTree sigsK catk hCatk = true := by decide +kernel

/-- Without the equation kept. -/
theorem catk_noeq : heapOkC Data.powTree sigsK catk { hCatk with eqs := [] } = false := by decide +kernel

/-- Without the exponents' facts. -/
theorem catk_noexp :
    heapOkC Data.powTree sigsK catk { hCatk with calls := [[.catM ⟨[(1, 1)], 0⟩ ⟨[(2, 1)], 0⟩ [], .run 0 [], .run 1 []]] } =
      false := by
  decide +kernel

/-- The parts swapped. -/
theorem catk_bad :
    heapOkC Data.powTree sigsK catk { hCatk with calls := [[.catM ⟨[(1, 1)], 0⟩ ⟨[(2, 1)], 0⟩ [0, 1], .run 1 [], .run 0 []]] } =
      false := by
  decide +kernel

/-! ## A merge with a root by an equation (round 6, E9) -/

/-- `fill2` as for `useM`; `readQ` needs `p·g^[0, e(q))`. -/
def sigsME (g : String) : HSig :=
  if g = "fill2" then sigsM "fill2"
  else if g = "readQ" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] } else .empty

/-- `q = n·n` (kept), calls `fill2` on `p, n`, then `readQ` on `p, q`. -/
def useME : Fn where
  name := "useME"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.mul (.n 2) (.n 1) (.n 1)), .call "fill2" [.n 0, .n 1] [], .call "readQ" [.n 0, .n 2] [], .ret []]

/-- `useME`'s certificate: `readQ`'s run merged from `fill2`'s two residues, the root `n` given (`mrgE`): `n²` is
`q` by the kept equation. -/
def hUseME : HCert where
  sig := {}
  reads := []
  res := [.lt (.num 0) (.val 1)]
  calls := [[], [.mrgE 2 ⟨[(1, 1)], 0⟩ [0], .run 0 [], .run 1 []]]
  rets := [[]]
  eqs := [2]

theorem useME_ok : heapOkC Data.powTree sigsME useME hUseME = true := by decide +kernel

/-- Without the equation. -/
theorem useME_noeq : heapOkC Data.powTree sigsME useME { hUseME with eqs := [] } = false := by decide +kernel

/-- `mrg` takes the root of `q` itself, which has no square root. -/
theorem useME_mrg :
    heapOkC Data.powTree sigsME useME { hUseME with calls := [[], [.mrg 2 [0], .run 0 [], .run 1 []]] } = false := by
  decide +kernel

/-! ## A block growing with the arm (round 6, E8) -/

/-- Arm `j` writes `p·g^[0, j + 1)`; `needX` needs `p·g^[0, e(x·g))`. -/
def sigsAb (g : String) : HSig :=
  if g = "blk0" then { post := [⟨[(0, 1)], 0⟩] }
  else if g = "blk1" then { post := [⟨[(0, 1)], 0⟩, ⟨[(0, 1)], 1⟩] }
  else if g = "needX" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .mono ⟨[(1, 1)], 1⟩⟩] } else .empty

/-- A dispatch on `x` over `blk0`, `blk1`, then `needX` on `p, x`. -/
def useAb : Fn where
  name := "useAb"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 1) ["blk0", "blk1"] [.n 0] [], .call "needX" [.n 0, .n 1] [], .ret []]

/-- `useAb`'s certificate: the block `ab p 1 1`, arm `j`'s run `p·g^[0, j + 1)` by its callee's points (`pts`);
after the dispatch, `p·g^[0, e(x·g))` at run serial `0`. -/
def hUseAb : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[.ab ⟨[(0, 1)], 0⟩ 1 1, .pts, .ev 0, .pts, .ev 0, .ev 1], [.run 0 []]]
  rets := [[]]

theorem useAb_ok : heapOkC Data.powTree sigsAb useAb hUseAb = true := by decide +kernel

/-- Arm `1`'s second cell not witnessed. -/
theorem useAb_bad :
    heapOkC Data.powTree sigsAb useAb { hUseAb with calls := [[.ab ⟨[(0, 1)], 0⟩ 1 1, .pts, .ev 0, .pts, .ev 0, .ev 0],
      [.run 0 []]] } = false := by
  decide +kernel

/-- A block one longer (`d = 2`): arm `0` writes one cell only. -/
theorem useAb_long :
    heapOkC Data.powTree sigsAb useAb { hUseAb with calls := [[.ab ⟨[(0, 1)], 0⟩ 1 2, .pts, .ev 0, .pts, .ev 0, .ev 1],
      [.run 0 []]] } = false := by
  decide +kernel

/-! ## A block whose base moves with the arm -/

/-- Arm `j` writes `p·g^(2j)`; `needM` needs `p·x^2`. -/
def sigsAbx (g : String) : HSig :=
  if g = "mv0" then { post := [⟨[(0, 1)], 0⟩] }
  else if g = "mv1" then { post := [⟨[(0, 1)], 2⟩] }
  else if g = "needM" then { pre := [⟨[(0, 1), (1, 2)], 0⟩] } else .empty

/-- A dispatch on `x` over `mv0`, `mv1`, then `needM` on `p, x`. -/
def useAbx : Fn where
  name := "useAbx"
  params := [.n 0, .n 1]
  body := [.dispatch (.n 1) ["mv0", "mv1"] [.n 0] [], .call "needM" [.n 0, .n 1] [], .ret []]

/-- `useAbx`'s certificate: the block `abx p 2 1 g^1 0`, arm `j`'s run `p·g^(2j)·g^[0, 1)` by its callee's point;
after the dispatch, `p·x^2·g^[0, 1)` at run serial `0`. -/
def hUseAbx : HCert where
  sig := {}
  reads := []
  res := []
  calls := [[.abx ⟨[(0, 1)], 0⟩ 2 1 ⟨[], 1⟩ 0, .pts, .ev 0, .pts, .ev 0], [.run 0 []]]
  rets := [[]]

theorem useAbx_ok : heapOkC Data.powTree sigsAbx useAbx hUseAbx = true := by decide +kernel

/-- The base moving by `1` an arm: arm `1`'s cell `p·g` not written. -/
theorem useAbx_bad :
    heapOkC Data.powTree sigsAbx useAbx { hUseAbx with calls := [[.abx ⟨[(0, 1)], 0⟩ 1 1 ⟨[], 1⟩ 0, .pts, .ev 0,
      .pts, .ev 0], [.run 0 []]] } = false := by
  decide +kernel

/-! ## Constant preconditions: the public input (round 6, E12) -/

/-- Reads the public input's cells `g^0[0]`, `g^0[1]` (`main`'s `pub_ptr`). -/
def pubRd : Fn where
  name := "pubRd"
  params := []
  body := [.atom (.const (.n 0) (word 1 0)), .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 0) 1), .ret []]

/-- `pubRd`'s certificate: the two cells constant preconditions (`preSet_const`). -/
def hPubRd : HCert where
  sig := { pre := [⟨[], 0⟩, ⟨[], 1⟩] }
  reads := [(1, [(0, 0, .pre 0)]), (2, [(0, 1, .pre 1)])]
  res := []
  rets := [[]]

theorem pubRd_ok : heapOkC Data.powTree (fun _ ↦ .empty) pubRd hPubRd = true := by decide +kernel

/-- Without them. -/
theorem pubRd_bad : heapOkC Data.powTree (fun _ ↦ .empty) pubRd { hPubRd with sig := {} } = false := by decide +kernel

/-! ## A loop's accumulated pointer run (round 6: `aggregate_claims_loop0`'s guarantee) -/

/-- Stores `s·i` at `q·i` for the counter `i` from its start to `n`. -/
def fillP : Fn where
  name := "fillP"
  params := [.n 0, .n 1, .n 2, .n 3]
  body := [.atom (.mul (.n 4) (.n 2) (.n 0)), .atom (.mul (.n 5) (.n 3) (.n 0)), .atom (.load (.n 5) (.n 4) 0),
    .atom (.const (.n 6) (word 2 0)), .atom (.mul (.n 7) (.n 0) (.n 6)), .atom (.add (.n 8) (.n 7) (.n 1)),
    .atom (.const (.n 9) (word 2 0)), .atom (.mul (.n 10) (.n 0) (.n 9)), .callIf (.n 8) "fillP" [.n 10, .n 1, .n 2, .n 3],
    .ret []]

/-- `fillP` writes, from its counter to its end, `q`'s cells each pointing to a written cell (`postPR`, offset `0`),
the cells `s·g^j` it points to its precondition. -/
def sigFillP : HSig :=
  { preR := [⟨⟨[(3, 1)], 0⟩, 1, .val 0, .val 1⟩], postPR := [(⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩, [0])],
    «term» := [(.val 0, .val 1)] }

/-- `fillP`'s certificate: the tail call's `preR` one further (shifted); the pointer run accumulated, the
counter's cell by the store's word (`word 0`) and the cell it points to by the own run at the counter. -/
def hFillP : HCert where
  sig := sigFillP
  reads := []
  res := []
  calls := [[.run 0 []]]
  rets := [[.word 0, .run 0 []]]

theorem fillP_ok : heapOkC Data.powTree (fun _ ↦ sigFillP) fillP hFillP = true := by decide +kernel

/-- The pointed cell witnessed by the store of the counter's cell. -/
theorem fillP_bad : heapOkC Data.powTree (fun _ ↦ sigFillP) fillP { hFillP with rets := [[.word 0, .ev 0]] } = false := by
  decide +kernel

/-- `fillP`, and `needP` needing `q`'s cells `[0, e(n))` pointing to written cells at offset `0`. -/
def sigsP2 (g : String) : HSig :=
  if g = "fillP" then sigFillP
  else if g = "needP" then { prePR := [(⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩, [0])] } else .empty

/-- Fills `q` from `g^0` to `n`, then calls `needP`. -/
def useFillP : Fn where
  name := "useFillP"
  params := [.n 0, .n 1, .n 2]
  body := [.atom (.const (.n 3) (word 1 0)), .call "fillP" [.n 3, .n 2, .n 0, .n 1] [], .call "needP" [.n 0, .n 2] [],
    .ret []]

/-- `useFillP`'s certificate: `fillP`'s `preR` its own (run serial `0`), `needP`'s pointer run `fillP`'s guarantee
(run serial `1`). -/
def hUseFillP : HCert where
  sig := { preR := [⟨⟨[(1, 1)], 0⟩, 1, .num 0, .val 2⟩] }
  reads := []
  res := []
  calls := [[.run 0 []], [.pfr 1 []]]
  rets := [[]]

theorem useFillP_ok : heapOkC Data.powTree sigsP2 useFillP hUseFillP = true := by decide +kernel

/-- Allocates two cells, writes them, stores the buffer's pointer at `o[0]`. -/
def mkq : Fn where
  name := "mkq"
  params := [.n 0]
  body := [.atom (.hint (.alloc (.n 1) 2)), .atom (.const (.n 2) (word 0 0)), .atom (.load (.n 2) (.n 1) 0),
    .atom (.load (.n 2) (.n 1) 1), .atom (.load (.n 1) (.n 0) 0), .ret []]

/-- `mkq`'s certificate: `o[0]` written, and the run of two cells at the word there (`postQ`), by the store of
`o[0]` (`word`) and the run's points. -/
def hMkq : HCert where
  sig := { post := [⟨[(0, 1)], 0⟩], postQ := [(⟨[(0, 1)], 0⟩, ⟨⟨[], 0⟩, 1, .num 0, .num 2⟩)] }
  reads := []
  res := []
  rets := [[.ev 2, .word 2, .pts, .ev 0, .ev 1]]

theorem mkq_ok : heapOkC Data.powTree (fun _ ↦ .empty) mkq hMkq = true := by decide +kernel

/-- A run of three cells at the word: its third cell is not written. -/
def hMkq3 : HCert where
  sig := { post := [⟨[(0, 1)], 0⟩], postQ := [(⟨[(0, 1)], 0⟩, ⟨⟨[], 0⟩, 1, .num 0, .num 3⟩)] }
  reads := []
  res := []
  rets := [[.ev 2, .word 2, .pts, .ev 0, .ev 1, .ev 1]]

theorem mkq_bad : heapOkC Data.powTree (fun _ ↦ .empty) mkq hMkq3 = false := by decide +kernel

/-- The run's word stored elsewhere (`word 0`: the store of `b[0]`, not of `o[0]`). -/
theorem mkq_bad2 : heapOkC Data.powTree (fun _ ↦ .empty) mkq
    { hMkq with rets := [[.ev 2, .word 0, .pts, .ev 0, .ev 1]] } = false := by decide +kernel

/-- Calls `mkq`, loads `o[0]`, reads the second cell past it. -/
def useq : Fn where
  name := "useq"
  params := [.n 0]
  body := [.call "mkq" [.n 0] [], .atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 1), .ret []]

/-- `useq`'s certificate: the call's `post` cell (point serial `0`); the load of `o[0]` puts the run at its word
into scope (run serial `0`). -/
def hUseq : HCert where
  sig := {}
  reads := [(1, [(0, 0, .ev 0)]), (2, [(1, 1, .run 0 [])])]
  res := []
  calls := [[]]
  rets := [[]]

theorem useq_ok : heapOkC Data.powTree (fun g ↦ if g = "mkq" then hMkq.sig else .empty) useq hUseq = true := by
  decide +kernel

/-- Without the load of `o[0]`, no run at its word is in scope. -/
theorem useq_bad : heapOkC Data.powTree (fun g ↦ if g = "mkq" then hMkq.sig else .empty)
    { useq with body := [.call "mkq" [.n 0] [], .atom (.load (.n 2) (.n 1) 1), .ret []] }
    { hUseq with reads := [(2, [(1, 1, .run 0 [])])] } = false := by
  decide +kernel

/-- Needs `p[0..k·g^4)` of `needQ` from its own `p[0..k)`, `p[k..k+2)`, `p[k+2..k+4)`: a `catM` at `k` whose part from
`k` is a `catM` at `g^2` (nested). -/
def catq : Fn where
  name := "catq"
  params := [.n 0, .n 1]
  body := [.call "needQ" [.n 0, .n 1] [], .ret []]

/-- `needQ (q, b)` needs `q[0..b·g^4)`. -/
def sigsCq : String → HSig := fun g ↦
  if g = "needQ" then { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .mono ⟨[(1, 1)], 4⟩⟩] } else .empty

/-- `catq`'s certificate: `catM k g^4`, its part from `k` `catM g^2 g^2`, each part a run in scope. -/
def hCatq : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩, ⟨⟨[(0, 1), (1, 1)], 0⟩, 1, .num 0, .num 2⟩,
    ⟨⟨[(0, 1), (1, 1)], 2⟩, 1, .num 0, .num 2⟩] }
  reads := []
  res := [.lt (.num 0) (.val 1)]
  calls := [[.catM ⟨[(1, 1)], 0⟩ ⟨[], 4⟩ [0], .run 0 [], .catM ⟨[], 2⟩ ⟨[], 2⟩ [], .run 1 [], .run 2 []]]
  rets := [[]]

theorem catq_ok : heapOkC Data.powTree sigsCq catq hCatq = true := by decide +kernel

/-- Two levels only: the last part split a third time. -/
theorem catq_bad : heapOkC Data.powTree sigsCq catq
    { hCatq with calls := [[.catM ⟨[(1, 1)], 0⟩ ⟨[], 4⟩ [0], .run 0 [], .catM ⟨[], 2⟩ ⟨[], 2⟩ [], .run 1 [],
      .catM ⟨[], 1⟩ ⟨[], 1⟩ [], .pts, .pts]] } = false := by decide +kernel

/-! ## An own parameter word -/

/-- Reads the word at `p[0]`, then through it. -/
def rdw : Fn where
  name := "rdw"
  params := [.n 0]
  body := [.atom (.load (.n 1) (.n 0) 0), .atom (.load (.n 2) (.n 1) 0), .ret []]

/-- `rdw`'s certificate: `p[0]` written (`pre`); ghost `0` (slot `1`, value `GB`) the word at `p[0]` (`gw`), its
cell `G·g^0` a precondition (`preR`), so the read through the word loaded at `p[0]` finds it. -/
def sRdw : HSig where
  pre := [⟨[(0, 1)], 0⟩]
  preR := [⟨⟨[(1, 1)], 0⟩, 1, .num 0, .num 1⟩]
  ghosts := 1
  gw := [(⟨[(0, 1)], 0⟩, 0)]

/-- `rdw`'s reads: `p[0]` by the precondition, the word's cell by the run. -/
def hRdw : HCert where
  sig := sRdw
  reads := [(1, [(0, 0, .pre 0)]), (2, [(1, 0, .run 0 [])])]
  res := []
  rets := [[]]

theorem rdw_ok : heapOkC Data.powTree (fun _ ↦ .empty) rdw hRdw = true := by decide +kernel

/-- Without the own parameter word, the word loaded is no ghost's. -/
theorem rdw_bad : heapOkC Data.powTree (fun _ ↦ .empty) rdw { hRdw with sig := { sRdw with gw := [] } } = false := by
  decide +kernel

/-- Writes `p·g^[0, 3)` then reads `p·i`, `e(i) < 3` by a residual: the run of the three write events (`evs`). -/
def evsRd : Fn where
  name := "evsRd"
  params := [.n 0, .n 1]
  body := [.atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 3) (.n 0) 1), .atom (.load (.n 4) (.n 0) 2),
    .atom (.mul (.n 5) (.n 0) (.n 1)), .atom (.load (.n 6) (.n 5) 0), .ret []]

def hEvsRd : HCert where
  sig := {}
  reads := [(6, [(5, 0, .evs 0 3 [0])])]
  res := [.lt (.val 1) (.num 3)]
  rets := [[]]

theorem evsRd_ok : heapOkC Data.powTree (fun _ ↦ .empty) evsRd hEvsRd = true := by decide +kernel

/-- `e(i) < 4`: `p·g^3` is not written. -/
theorem evsRd_far : heapOkC Data.powTree (fun _ ↦ .empty) evsRd
    { hEvsRd with reads := [(6, [(5, 0, .evs 0 4 [0])])], res := [.lt (.val 1) (.num 4)] } = false := by
  decide +kernel

/-- From the second event: its cells are `p·g^[1, 3)`, not from `p`. -/
theorem evsRd_shift : heapOkC Data.powTree (fun _ ↦ .empty) evsRd
    { hEvsRd with reads := [(6, [(5, 0, .evs 1 2 [0])])], res := [.lt (.val 1) (.num 2)] } = false := by
  decide +kernel

/-- Writes `p·g^0` and `p·g`, has `p·g·g^[1, e(n))` and reads `p·n`: in the run when `e(n) ≥ 2`, else one of the
two points (`back`). -/
def backRd : Fn where
  name := "backRd"
  params := [.n 0, .n 1]
  body := [.atom (.load (.n 2) (.n 0) 0), .atom (.load (.n 3) (.n 0) 1),
    .atom (.mul (.n 4) (.n 0) (.n 1)), .atom (.load (.n 5) (.n 4) 0), .ret []]

def hBackRd : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 1⟩, 1, .num 1, .val 1⟩] }
  reads := [(5, [(4, 0, .back 0 [0, 1] [0])])]
  res := [.lt (.val 1) (.num 100)]
  rets := [[]]

theorem backRd_ok : heapOkC Data.powTree (fun _ ↦ .empty) backRd hBackRd = true := by decide +kernel

/-- Without the point for `e(n) = 1`. -/
theorem backRd_short : heapOkC Data.powTree (fun _ ↦ .empty) backRd
    { hBackRd with reads := [(5, [(4, 0, .back 0 [0] [0])])] } = false := by decide +kernel

/-- The points in the wrong order. -/
theorem backRd_swap : heapOkC Data.powTree (fun _ ↦ .empty) backRd
    { hBackRd with reads := [(5, [(4, 0, .back 0 [1, 0] [0])])] } = false := by decide +kernel

/-- Guarantees `p·g^[0, e(n))` from `p·g^[0, 40)`, `e(n) < 41` by a fact (`hiOk`, the upper bound's next). -/
def hiLe : Fn where
  name := "hiLe"
  params := [.n 0, .n 1]
  body := [.ret []]

def hHiLe : HCert where
  sig := { preR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .num 40⟩], postR := [⟨⟨[(0, 1)], 0⟩, 1, .num 0, .val 1⟩] }
  reads := []
  res := [.lt (.val 1) (.num 41)]
  rets := [[.run 0 [0]]]

theorem hiLe_ok : heapOkC Data.powTree (fun _ ↦ .empty) hiLe hHiLe = true := by decide +kernel

/-- `e(n) < 42` is not enough. -/
theorem hiLe_bad : heapOkC Data.powTree (fun _ ↦ .empty) hiLe { hHiLe with res := [.lt (.val 1) (.num 42)] } =
    false := by
  decide +kernel

end

end LeanVM.Guest.CoreMode.Test
