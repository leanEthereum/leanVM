/-
  LeanVM.Guest.CoreMode.HeapCTest

  The heap check with calls and loops on hand-written certificates: two loop helpers and a caller
  of the guest, and small functions for returned words, runs consumed and a dispatch.
-/

module

public import LeanVM.Guest.CoreMode.HeapC
public import LeanVM.Guest.Data.Pows
public import LeanVM.Guest.Pack.«P0».Core
public import LeanVM.Guest.Pack.«P53».Core
public import LeanVM.Guest.Pack.«P56».Core

/-!
# Tests of `heapOkC`

Certificates written by hand, each checked by the kernel (`decide +kernel`), and a wrong witness
rejected.

* `__loop7` (`verify_bus_gkr_loop1`): reads `p3·i` (its own `preR`, at its counter by the
  termination fact), stores at `p2·i` (its `postR`, accumulated), its tail call's `preR` one further
  (the shifted lower bound).
* `__loop23` (`da_pad_loop0`): two accumulated runs of stride 2 over `p2·p3²`.
* `opening_round`: reads `p5[0..4]` (preconditions), calls `grind_check__L7` (empty signature here),
  stores `p8[0]`, `p9[0]`, `p9[1]` (its guarantees).
* `mk`, `useMk`: a guarantee over a returned word, read by the caller after the call; `useMk2`, the
  same through a `dispatch` of two arms.
* `fill`, `useFill`: a loop's accumulated run `p·g^j`, `j < e(n)`, read by its caller at the constant
  index `3` (a residual `3 < e(n)`) and passed whole to a second loop's `preR`; `useFillIf`, the loop
  entered by a `callIf` whose guard is `g^0 + n`, its run pushed (`callIfR`); `useFillX`, reads at the
  indices `x` and `x·g^3` of the run, by residuals on a value and on a monomial (`idx`, `CIdx.mono`).
-/

namespace LeanVM.Guest.CoreMode.Test

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Loop helpers of the guest -/

/-- `__loop7`'s certificate. -/
def h7 : HCert where
  sig := ⟨[], [], [⟨⟨[(3, 1)], 0⟩, 1, .val 0, .val 1⟩], [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩],
    [(.val 0, .val 1)]⟩
  reads := [(5, [(4, 0, .run 0 [])])]
  res := []
  calls := [[.run 0 []]]
  rets := [[.ev 1]]

theorem loop7_ok : heapOkC Data.powTree (fun _ ↦ h7.sig) Fn.«verify_bus_gkr_loop1».core h7 = true := by
  decide +kernel

/-- The point at the counter not written: the store's serial is `1`, not `0`. -/
theorem loop7_bad :
    heapOkC Data.powTree (fun _ ↦ h7.sig) Fn.«verify_bus_gkr_loop1».core { h7 with rets := [[.ev 0]] } = false := by
  decide +kernel

/-- `__loop23`'s certificate. -/
def h23 : HCert where
  sig := ⟨[], [], [], [⟨⟨[(2, 1), (3, 2)], 0⟩, 2, .val 0, .val 1⟩, ⟨⟨[(2, 1), (3, 2)], 1⟩, 2, .val 0, .val 1⟩],
    [(.val 0, .val 1)]⟩
  reads := []
  res := []
  calls := [[]]
  rets := [[.ev 0, .ev 1]]

theorem loop23_ok : heapOkC Data.powTree (fun _ ↦ h23.sig) Fn.«da_pad_loop0».core h23 = true := by
  decide +kernel

/-! ## A caller of the guest -/

/-- `opening_round`'s certificate, `grind_check__L7`'s signature taken empty. -/
def hOR : HCert where
  sig := ⟨[⟨[(5, 1)], 0⟩, ⟨[(5, 1)], 1⟩, ⟨[(5, 1)], 2⟩, ⟨[(5, 1)], 3⟩, ⟨[(5, 1)], 4⟩],
    [⟨[(8, 1)], 0⟩, ⟨[(9, 1)], 0⟩, ⟨[(9, 1)], 1⟩], [], [], []⟩
  reads := [(15, [(5, 0, .pre 0)]), (18, [(5, 1, .pre 1)]), (21, [(5, 2, .pre 2)]), (24, [(5, 3, .pre 3)]),
    (40, [(5, 4, .pre 4)])]
  res := []
  calls := [[]]
  rets := [[.ev 5, .ev 6, .ev 7]]

theorem openingRound_ok :
    heapOkC Data.powTree (fun g ↦ if g = "opening_round" then hOR.sig else .empty) Fn.«opening_round».core hOR =
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
  sig := ⟨[], [⟨[(1, 1)], 0⟩, ⟨[(1, 1)], 1⟩], [], [], []⟩
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
  hFill : HSig := ⟨[], [], [], [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩], [(.val 0, .val 1)]⟩
  hReadAll : HSig := ⟨[], [], [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩], [], []⟩

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
  sig := ⟨sigs.hReadAll.pre, [], sigs.hReadAll.preR, [], [(.val 0, .val 1)]⟩
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

end

end LeanVM.Guest.CoreMode.Test
