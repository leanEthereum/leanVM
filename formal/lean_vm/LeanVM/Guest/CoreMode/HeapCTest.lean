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
* `off2`, `useOff2`, `useOff2D`: a returned word `p·g^2` (`retM`), read through by the caller, after a
  call and after a `dispatch`; `hvf`: a word stored, read back and read through (`hv`); `divf`: a
  quotient by `g` (`divs`).
-/

namespace LeanVM.Guest.CoreMode.Test

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! ## Loop helpers of the guest -/

/-- `__loop7`'s certificate. -/
def h7 : HCert where
  sig :=
    { preR := [⟨⟨[(3, 1)], 0⟩, 1, .val 0, .val 1⟩], postR := [⟨⟨[(2, 1)], 0⟩, 1, .val 0, .val 1⟩],
      «term» := [(.val 0, .val 1)] }
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
  sig :=
    { postR := [⟨⟨[(2, 1), (3, 2)], 0⟩, 2, .val 0, .val 1⟩, ⟨⟨[(2, 1), (3, 2)], 1⟩, 2, .val 0, .val 1⟩],
      «term» := [(.val 0, .val 1)] }
  reads := []
  res := []
  calls := [[]]
  rets := [[.ev 0, .ev 1]]

theorem loop23_ok : heapOkC Data.powTree (fun _ ↦ h23.sig) Fn.«da_pad_loop0».core h23 = true := by
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

end

end LeanVM.Guest.CoreMode.Test
